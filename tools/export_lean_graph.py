#!/usr/bin/env python3
"""Project checked Lean expression references into patrik-cihal/lean-graph JSON.

Consumes the existing lossless RH expression index, NOT source regexes or
instance-filtered dependencies. Output is a bounded declaration graph, not AST.
"""
from __future__ import annotations
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path

from rh_graph_explorer import GraphStore

CATEGORIES = {'thm': 'Theorem', 'def': 'Definition',
              'opaque': 'Definition', 'axiom': 'Axiom'}


def references(store, declaration, budget):
    """Collect all constants in checked type and proof-value Expr DAGs."""
    stack = list(declaration['expression_roots'])
    seen, refs = set(), set()
    while stack:
        idx = stack.pop()
        if idx in seen:
            continue
        if len(seen) >= budget:
            raise ValueError('expression budget exhausted for ' + declaration['name'])
        seen.add(idx)
        expr = store.expression(idx)
        ref = expr.get('reference')
        if ref is not None:
            if not ref['defined']:
                raise ValueError('unresolved Name ID ' + str(ref['name_id']))
            refs.add(ref['name_id'])
        stack.extend(ch['id'] for ch in expr['children'])
    return refs


def project(store, roots, depth=2, max_nodes=500, max_expr=500000):
    if depth < 0 or max_nodes < 1 or max_expr < 1:
        raise ValueError('invalid depth or resource budget')
    if not roots or len(set(roots)) != len(roots):
        raise ValueError('root names must be unique and nonempty')
    ids = []
    for root in roots:
        d = store.declaration(root)
        if d is None or d['kind'] != 'thm':
            raise ValueError('missing or non-theorem root: ' + root)
        ids.append(d['id'])
    if len(set(ids)) != len(ids) or len(ids) > max_nodes:
        raise ValueError('duplicate root or node budget exhausted')
    levels = dict.fromkeys(ids, 0)
    queue = deque(ids)
    declarations, edges = {}, {}
    while queue:
        ident = queue.popleft()
        d = store.declaration(name_id=ident)
        if d is None:
            raise ValueError('unknown referenced declaration ' + str(ident))
        declarations[ident] = d
        if levels[ident] == depth:
            edges[ident] = set()
            continue
        refs = references(store, d, max_expr)
        edges[ident] = refs
        for ref_id in sorted(refs):
            if ref_id in levels:
                continue
            if len(levels) >= max_nodes:
                raise ValueError('node budget exhausted; increase --max-nodes or reduce --depth')
            levels[ref_id] = levels[ident] + 1
            queue.append(ref_id)
    # Upstream Lean Graph keys nodes by printed names. Distinguish colliding IDs.
    counts = {}
    for d in declarations.values():
        counts[d['name']] = counts.get(d['name'], 0) + 1
    labels = {i: d['name'] + (f' [Name ID {i}]' if counts[d['name']] > 1 else '')
              for i, d in declarations.items()}
    data = [{
        'name': labels[i],
        'references': sorted(labels[j] for j in edges[i]),
        'constCategory': CATEGORIES.get(d['kind'], 'Other'),
        'constType': f"Kernel type Expr ID {d['expression_roots'][0]} (not pretty-printed)",
    } for i, d in sorted(declarations.items(), key=lambda x: (levels[x[0]], labels[x[0]]))]
    receipt = {
        'format': 'patrik-cihal/lean-graph node array',
        'source': 'checked exported type and proof-value references',
        'source_manifest': store.manifest,
        'root_names': list(roots),
        'root_name_ids': ids,
        'depth': depth,
        'node_count': len(data),
        'boundary_count': sum(v == depth for v in levels.values()),
        'complete_transitive_closure': False,
        'identity': [{'name_id': i, 'name': d['name'], 'label': labels[i], 'depth': levels[i]}
                     for i, d in sorted(declarations.items())],
        'warning': 'Depth-bounded declaration projection, not a full proof AST, '
                   'independent kernel check, or source-pruning certificate.',
    }
    return data, receipt


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--index-dir', type=Path, required=True)
    p.add_argument('--root', action='append', required=True)
    p.add_argument('--depth', type=int, default=2)
    p.add_argument('--max-nodes', type=int, default=500)
    p.add_argument('--max-expr-per-declaration', type=int, default=500000)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    receipt_path = a.output.with_suffix('.manifest.json')
    if a.output.exists() or receipt_path.exists():
        p.error('output exists; refusing overwrite')
    store = GraphStore(a.index_dir)
    try:
        nodes, receipt = project(store, tuple(a.root), a.depth, a.max_nodes,
                                 a.max_expr_per_declaration)
    finally:
        store.close()
    payload = (json.dumps(nodes, indent=2, ensure_ascii=False) + '\n').encode()
    receipt['node_json_sha256'] = hashlib.sha256(payload).hexdigest()
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_bytes(payload)
    receipt_path.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n')
    print(f'Exported {len(nodes)} declarations to {a.output}')
    print(f'Open it at https://patrik-cihal.github.io/lean-graph/')


if __name__ == '__main__':
    main()
