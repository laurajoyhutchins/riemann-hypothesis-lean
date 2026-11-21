#!/usr/bin/env python3
"""Build and serve a lazy, lossless index of the pinned lean4export Expr DAG.

The original export_exact_graph.py remains authoritative for five-root closure
counts. This companion reuses its Expr edge validation, but indexes full Expr
payloads and declaration records for interactive, on-demand inspection.

Build (after verifying the source export's compressed SHA-256):
  zstd -d --long=30 -c solution.ndjson.zst |
      python3 tools/rh_graph_explorer.py build --output-dir analysis/viewer
Serve locally (never exposes a network listener by default):
  python3 tools/rh_graph_explorer.py serve --index-dir analysis/viewer
"""
from __future__ import annotations

import argparse
import hashlib
from http.server import BaseHTTPRequestHandler, HTTPServer
import json
import os
from pathlib import Path
import sqlite3
import struct
import sys
import tempfile
from threading import local
from urllib.parse import parse_qs, urlsplit
import zlib

from export_exact_graph import KINDS, ROOTS, expr_record

# Each expression is stored as a (block, offset, length) triple. Blocks are
# independently zlib-compressed, so opening one Expr never decompresses the DAG.
LOCATION = struct.Struct('<III')
BLOCK = struct.Struct('<QII')       # compressed offset, compressed length, raw length
BLOCK_LIMIT = 1 << 20             # 1 MiB per independent block
FORMAT = 'rh-lean4export-expr-index-v1'


def compact(obj):
    return json.dumps(obj, separators=(',', ':'), ensure_ascii=False)


class PackedExprWriter:
    def __init__(self, directory):
        self.payload = (directory / 'expr.blocks').open('wb')
        self.locations = (directory / 'expr.locations').open('wb')
        self.blocks = (directory / 'expr.block-index').open('wb')
        self.buffer = bytearray()
        self.block_count = 0
        self.expr_count = 0

    def put(self, raw):
        if len(raw) > 0xFFFFFFFF:
            raise ValueError('single Expr payload exceeds 32-bit offset field')
        if self.buffer and len(self.buffer) + len(raw) > BLOCK_LIMIT:
            self.flush()
        if len(self.buffer) + len(raw) > 0xFFFFFFFF:
            raise ValueError('Expr block exceeds 32-bit offset field')
        self.locations.write(LOCATION.pack(self.block_count, len(self.buffer), len(raw)))
        self.buffer.extend(raw)
        self.expr_count += 1

    def flush(self):
        if not self.buffer:
            return
        compressed = zlib.compress(self.buffer, level=3)
        self.blocks.write(BLOCK.pack(self.payload.tell(), len(compressed), len(self.buffer)))
        self.payload.write(compressed)
        self.buffer.clear()
        self.block_count += 1

    def close(self):
        self.flush()
        self.payload.close()
        self.locations.close()
        self.blocks.close()


def _entries(obj):
    if 'inductive' in obj:
        block = obj['inductive']
        entries = []
        for aliases, kind in ((('types', 'inductiveVals'), 'inductive_type'),
                              (('ctors', 'constructorVals'), 'constructor'),
                              (('recs', 'recursorVals'), 'recursor')):
            for alias in aliases:
                if alias in block:
                    entries.extend((kind, e) for e in block[alias])
                    break
        group = [e['name'] for _, e in entries]
        for kind, entry in entries:
            roots = [entry['type']]
            if kind == 'recursor':
                roots.extend(rule['rhs'] for rule in entry['rules'])
            yield kind, entry, roots, group
    else:
        for kind in KINDS:
            if kind in obj:
                entries = obj[kind]
                if isinstance(entries, dict):
                    entries = [entries]
                group = [e['name'] for e in entries] if kind == 'quot' else []
                for entry in entries:
                    roots = [entry['type']]
                    if kind in ('def', 'thm', 'opaque'):
                        roots.append(entry['value'])
                    yield kind, entry, roots, list(entry.get('all', [])) + group
                break


def _schema(db):
    db.executescript('''
        CREATE TABLE names (id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE);
        CREATE TABLE declarations (
          name_id INTEGER PRIMARY KEY, kind TEXT NOT NULL,
          roots TEXT NOT NULL, grouped TEXT NOT NULL, raw TEXT NOT NULL
        );
    ''')


def build_index(stream, output_dir, roots=ROOTS, compressed_sha256=None):
    """Build atomically; on malformed/incomplete input never publish an index."""
    output_dir = Path(output_dir)
    if output_dir.exists():
        raise FileExistsError(f'index destination exists: {output_dir}')
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.rh-expr-', dir=output_dir.parent) as temp:
        temp = Path(temp)
        db = sqlite3.connect(temp / 'index.sqlite3')
        _schema(db)
        writer = PackedExprWriter(temp)
        names = ['']
        declared = bytearray(1)
        referenced = bytearray(1)
        decl_count = 0
        metadata = None
        input_hash = hashlib.sha256()
        pending_names = []
        pending_decls = []

        def flush_rows():
            if pending_names:
                db.executemany('INSERT INTO names (id,name) VALUES (?,?)', pending_names)
                pending_names.clear()
            if pending_decls:
                db.executemany('INSERT INTO declarations VALUES (?,?,?,?,?)', pending_decls)
                pending_decls.clear()
            db.commit()

        try:
            for raw in stream:
                input_hash.update(raw)
                if b'"ie":' in raw:
                    obj = json.loads(raw)
                    idx = writer.expr_count
                    name, *_ = struct.unpack('<IIII', expr_record(obj, idx))
                    if name:
                        if name >= len(names):
                            raise ValueError(f'Expr {idx} references unknown Name ID {name}')
                        referenced[name] = 1
                    writer.put(raw)
                    continue
                if not (b'"in":' in raw or b'"meta":' in raw or any(
                        ('"' + key + '":').encode() in raw for key in (*KINDS, 'inductive'))):
                    continue
                obj = json.loads(raw)
                if 'meta' in obj:
                    if metadata is not None:
                        raise ValueError('duplicate metadata')
                    metadata = obj['meta']
                elif 'in' in obj:
                    idx = obj['in']
                    if idx != len(names):
                        raise ValueError(f'nonconsecutive Name ID {idx}')
                    part = obj.get('str', obj.get('num'))
                    if part is None or not isinstance(part.get('pre'), int):
                        raise ValueError(f'invalid Name constructor at {idx}')
                    parent = part['pre']
                    if not 0 <= parent < idx:
                        raise ValueError(f'bad Name parent {parent} at {idx}')
                    suffix = part.get('str', str(part.get('i')))
                    if not isinstance(suffix, str):
                        raise ValueError(f'invalid Name suffix at {idx}')
                    name = names[parent] + ('.' if names[parent] else '') + suffix
                    names.append(name)
                    declared.append(0)
                    referenced.append(0)
                    pending_names.append((idx, name))
                else:
                    for kind, entry, exprs, group in _entries(obj):
                        name_id = entry['name']
                        if not isinstance(name_id, int) or not 0 < name_id < len(names):
                            raise ValueError(f'bad declaration Name ID {name_id}')
                        if declared[name_id]:
                            raise ValueError(f'duplicate declaration: {names[name_id]}')
                        if any(not isinstance(x, int) or not 0 <= x < writer.expr_count for x in exprs):
                            raise ValueError(f'declaration {names[name_id]} refers to absent Expr')
                        if any(not isinstance(x, int) or not 0 < x < len(names) for x in group):
                            raise ValueError(f'declaration {names[name_id]} has invalid group')
                        declared[name_id] = 1
                        decl_count += 1
                        pending_decls.append((name_id, kind, compact(exprs), compact(group), compact(entry)))
                if len(pending_names) + len(pending_decls) >= 4096:
                    flush_rows()
            flush_rows()
            if metadata is None or writer.expr_count == 0 or decl_count == 0:
                raise ValueError('missing export metadata, Exprs, or declarations')
            unresolved = [names[i] for i in range(1, len(names)) if referenced[i] and not declared[i]]
            if unresolved:
                raise ValueError(f'export contains {len(unresolved)} unresolved constants, e.g. {unresolved[:8]}')
            roots = tuple(roots)
            if not roots or len(set(roots)) != len(roots):
                raise ValueError('root set must be nonempty and unique')
            found = db.execute('SELECT n.name, d.kind FROM names n JOIN declarations d ON n.id=d.name_id WHERE n.name IN (' +
                               ','.join('?' for _ in roots) + ')', roots).fetchall()
            found = dict(found)
            if any(found.get(root) != 'thm' for root in roots):
                raise ValueError(f'missing or non-theorem roots: {[root for root in roots if found.get(root) != "thm"]}')
            writer.close()
            result = {
                'format': FORMAT,
                'roots': roots,
                'name_count': len(names) - 1,
                'declaration_count': decl_count,
                'expression_count': writer.expr_count,
                'compressed_blocks': writer.block_count,
                'export_metadata': metadata,
                'decompressed_ndjson_sha256': input_hash.hexdigest(),
                'compressed_input_sha256_supplied_not_checked': compressed_sha256,
                'unresolved_constant_count': 0,
                'complete_index': True,
                'warning': 'Index completeness is not independent Lean kernel verification or a source-pruning certificate.'
            }
            (temp / 'manifest.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
            db.execute('CREATE INDEX names_prefix ON names(name)')
            db.commit()
            db.close()
            temp.rename(output_dir)
            return result
        finally:
            if not writer.payload.closed:
                writer.close()
            db.close()


class GraphStore:
    def __init__(self, path):
        self.path = Path(path)
        self.manifest = json.loads((self.path / 'manifest.json').read_text(encoding='utf-8'))
        if self.manifest.get('format') != FORMAT or not self.manifest.get('complete_index'):
            raise ValueError('unsupported or incomplete graph index')
        self.con = sqlite3.connect(f'file:{(self.path / "index.sqlite3").resolve()}?mode=ro', uri=True, check_same_thread=False)
        self.payload = (self.path / 'expr.blocks').open('rb')
        self.locations = (self.path / 'expr.locations').open('rb')
        self.blocks = (self.path / 'expr.block-index').open('rb')
        self.cached_block_id = None
        self.cached_block = b''

    def close(self):
        self.con.close()
        self.payload.close()
        self.locations.close()
        self.blocks.close()

    def find(self, prefix, limit=30):
        if not prefix or len(prefix) > 250 or not 1 <= limit <= 100:
            raise ValueError('prefix length must be 1..250; limit 1..100')
        # Range query uses the indexed full Name and avoids a full-table LIKE scan.
        # U+10FFFF gives a strict upper bound on all names extending this prefix.
        rows = self.con.execute('SELECT name FROM names WHERE name>=? AND name<? ORDER BY name LIMIT ?',
                                (prefix, prefix + chr(0x10FFFF), limit)).fetchall()
        return [r[0] for r in rows]

    def declaration(self, name):
        row = self.con.execute('''SELECT n.id,d.kind,d.roots,d.grouped,d.raw
            FROM declarations d JOIN names n ON n.id=d.name_id WHERE n.name=?''', (name,)).fetchone()
        if row is None:
            return None
        return {'name': name, 'id': row[0], 'kind': row[1],
                'expression_roots': json.loads(row[2]), 'mutual_or_group': json.loads(row[3]),
                'raw': json.loads(row[4])}

    def _name(self, ident):
        row = self.con.execute('SELECT name FROM names WHERE id=?', (ident,)).fetchone()
        return row[0] if row else None

    def expression(self, idx):
        if not isinstance(idx, int) or not 0 <= idx < self.manifest['expression_count']:
            raise ValueError('Expr ID out of range')
        self.locations.seek(idx * LOCATION.size)
        data = self.locations.read(LOCATION.size)
        if len(data) != LOCATION.size:
            raise ValueError('truncated Expr locations')
        block_id, offset, length = LOCATION.unpack(data)
        if block_id != self.cached_block_id:
            self.blocks.seek(block_id * BLOCK.size)
            record = self.blocks.read(BLOCK.size)
            if len(record) != BLOCK.size:
                raise ValueError('truncated Expr block index')
            c_offset, c_size, raw_size = BLOCK.unpack(record)
            self.payload.seek(c_offset)
            raw = self.payload.read(c_size)
            if len(raw) != c_size:
                raise ValueError('truncated Expr block')
            data = zlib.decompress(raw)
            if len(data) != raw_size:
                raise ValueError('bad decompressed Expr block length')
            self.cached_block = data
            self.cached_block_id = block_id
        if offset + length > len(self.cached_block):
            raise ValueError('Expr location exceeds block')
        obj = json.loads(self.cached_block[offset: offset + length])
        if obj.get('ie') != idx:
            raise ValueError('Expr index mismatch')
        children = []
        reference = None
        if 'app' in obj:
            children = [('fn', obj['app']['fn']), ('arg', obj['app']['arg'])]
        elif 'lam' in obj or 'forallE' in obj:
            data = obj.get('lam', obj.get('forallE'))
            children = [('type', data['type']), ('body', data['body'])]
        elif 'letE' in obj:
            data = obj['letE']
            children = [('type', data['type']), ('value', data['value']), ('body', data['body'])]
        elif 'mdata' in obj:
            children = [('expr', obj['mdata']['expr'])]
        elif 'proj' in obj:
            children = [('struct', obj['proj']['struct'])]
            reference = obj['proj']['typeName']
        elif 'const' in obj:
            reference = obj['const']['name']
        kind = next((k for k in ('app', 'lam', 'forallE', 'letE', 'mdata', 'proj', 'const',
                                 'bvar', 'sort', 'natVal', 'strVal') if k in obj), 'unknown')
        result = {'id': idx, 'kind': kind,
                  'children': [{'role': k, 'id': v} for k, v in children], 'raw': obj}
        if reference is not None:
            result['reference'] = {'name_id': reference, 'name': self._name(reference)}
            r = self.con.execute('SELECT 1 FROM declarations WHERE name_id=?', (reference,)).fetchone()
            result['reference']['defined'] = bool(r)
        return result


def handler_factory(index_dir, viewer_path):
    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            try:
                u = urlsplit(self.path)
                query = parse_qs(u.query)
                if u.path == '/':
                    data = Path(viewer_path).read_bytes()
                    self._send(200, data, 'text/html; charset=utf-8')
                    return
                if u.path == '/api/manifest':
                    self._json(200, self.server.store.manifest)
                    return
                if u.path == '/api/find':
                    self._json(200, {'matches': self.server.store.find(query.get('q', [''])[0])})
                    return
                if u.path == '/api/declaration':
                    name = query.get('name', [''])[0]
                    if not name or len(name) > 2048:
                        raise ValueError('declaration name missing or too long')
                    result = self.server.store.declaration(name)
                    self._json(200, result) if result is not None else self._json(404, {'error': 'unknown declaration'})
                    return
                if u.path == '/api/expression':
                    raw = query.get('id', [''])[0]
                    if not raw.isdecimal():
                        raise ValueError('invalid expression ID')
                    self._json(200, self.server.store.expression(int(raw)))
                    return
                self._json(404, {'error': 'not found'})
            except (ValueError, KeyError) as exc:
                self._json(400, {'error': str(exc)})

        def _json(self, status, value):
            self._send(status, compact(value).encode('utf-8'), 'application/json; charset=utf-8')

        def _send(self, status, data, content_type):
            self.send_response(status)
            self.send_header('Content-Type', content_type)
            self.send_header('Content-Length', str(len(data)))
            self.send_header('Cache-Control', 'no-store')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.send_header('Content-Security-Policy', "default-src 'none'; style-src 'unsafe-inline'; script-src 'unsafe-inline'; connect-src 'self'")
            self.end_headers()
            self.wfile.write(data)

    return Handler


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    build = commands.add_parser('build')
    build.add_argument('--output-dir', type=Path, required=True)
    build.add_argument('--root', action='append')
    build.add_argument('--compressed-sha256', help='provenance only: verify upstream before decompression')
    serve = commands.add_parser('serve')
    serve.add_argument('--index-dir', type=Path, required=True)
    serve.add_argument('--port', type=int, default=8765)
    args = parser.parse_args()
    if args.command == 'build':
        result = build_index(sys.stdin.buffer, args.output_dir, tuple(args.root) if args.root else ROOTS,
                             compressed_sha256=args.compressed_sha256)
        print(json.dumps(result, indent=2))
    else:
        store = GraphStore(args.index_dir)
        try:
            server = HTTPServer(('127.0.0.1', args.port),
                                         handler_factory(args.index_dir, Path(__file__).with_name('rh_graph_viewer.html')))
            server.store = store
            print(f'Explore http://127.0.0.1:{server.server_port}/', flush=True)
            server.serve_forever()
        finally:
            store.close()


if __name__ == '__main__':
    main()