"""Exact independent geometry for FORMAT.md; Python standard library only.

No producer code or SAT library is imported. All coordinates and operations
are integers. A vertex link is tested by edge connectivity, without angles.
"""
from collections import defaultdict
from functools import lru_cache


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(x):
    return type(x) is int


def valid_cell(family, c):
    return family != "iamond" or (c[0] % 3 == c[1] % 3 and c[0] % 3 in (0, 1))


def cells(value, family):
    require(isinstance(value, list) and len(value) > 0, "empty/non-list cells")
    require(all(isinstance(c, list) and len(c) == 2 and all(integer(x) for x in c)
                for c in value), "non-integer coordinate")
    result = frozenset(tuple(c) for c in value)
    require(len(result) == len(value), "duplicate cell")
    require(all(valid_cell(family, c) for c in result), "invalid lattice coordinate")
    return result


@lru_cache(maxsize=100000)
def vertices(family, c):
    x, y = c
    if family == "omino":
        return ((x, y), (x+1, y), (x+1, y+1), (x, y+1))
    if family == "hex":
        # Vertex coordinates multiplied by 3 in the oblique basis.
        return tuple((3*x+a, 3*y+b) for a, b in
                     ((1, 1), (-1, 2), (-2, 1), (-1, -1), (1, -2), (2, -1)))
    require(family == "iamond" and valid_cell(family, c), "unknown family/cell")
    offsets = ((-1, 2), (-1, -1), (2, -1)) if x % 3 == 0 else ((1, -2), (1, 1), (-2, 1))
    return tuple((x+a, y+b) for a, b in offsets)


@lru_cache(maxsize=100000)
def neighbors(family, c, edge=False):
    x, y = c
    if family == "omino":
        return frozenset((x+a, y+b) for a in (-1, 0, 1) for b in (-1, 0, 1)
                         if (a or b) and (not edge or abs(a)+abs(b) == 1))
    if family == "hex":
        return frozenset((x+a, y+b) for a, b in ((1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)))
    # All six incident triangle centres obtained from each vertex. A shared
    # edge means exactly two common vertices. No floating point geometry.
    vc = set(vertices(family, c))
    candidates = set()
    for vx, vy in vc:
        for dx, dy in ((1, -2), (1, 1), (-2, 1), (-1, 2), (-1, -1), (2, -1)):
            z = vx+dx, vy+dy
            if z != c and valid_cell(family, z):
                candidates.add(z)
    return frozenset(z for z in candidates
                     if len(vc.intersection(vertices(family, z))) >= (2 if edge else 1))


def halo(family, patch):
    return frozenset(n for c in patch for n in neighbors(family, c) if n not in patch)


def components(nodes, adjacency):
    remaining = set(nodes)
    result = []
    while remaining:
        start = remaining.pop()
        comp, todo = {start}, [start]
        while todo:
            c = todo.pop()
            new = remaining.intersection(adjacency(c))
            remaining.difference_update(new)
            comp.update(new)
            todo.extend(new)
        result.append(frozenset(comp))
    return result


def holes(family, patch):
    margin = 6 if family == "iamond" else 2
    xmin = min(c[0] for c in patch)-margin
    xmax = max(c[0] for c in patch)+margin
    ymin = min(c[1] for c in patch)-margin
    ymax = max(c[1] for c in patch)+margin
    require((xmax-xmin+1)*(ymax-ymin+1) <= 2_000_000, "bounding box exceeds checker resource cap")
    complement = {(x, y) for x in range(xmin, xmax+1) for y in range(ymin, ymax+1)
                  if (x, y) not in patch and valid_cell(family, (x, y))}
    comps = components(complement, lambda c: neighbors(family, c, True))
    # A component is exterior iff an edge can leave the padded box.
    return [comp for comp in comps if not any(
        n[0] < xmin or n[0] > xmax or n[1] < ymin or n[1] > ymax
        for c in comp for n in neighbors(family, c, True))]


def disk_details(family, patch):
    edge_components = len(components(patch, lambda c: neighbors(family, c, True)))
    bounded = holes(family, patch)
    incident = defaultdict(set)
    for c in patch:
        for v in vertices(family, c):
            incident[v].add(c)
    bad_vertices = []
    for v, around in incident.items():
        if len(components(around, lambda c: neighbors(family, c, True))) > 1:
            bad_vertices.append(v)
    return {"disk": edge_components == 1 and not bounded and not bad_vertices,
            "edge_components": edge_components, "holes": len(bounded),
            "hole_sizes": sorted(map(len, bounded)), "bad_vertices": sorted(bad_vertices)}


def matmul(m, n):
    a, b, c, d = m
    e, f, g, h = n
    return a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h


def transform(m, c):
    a, b, d, e = m
    x, y = c
    return a*x+b*y, d*x+e*y


def matrices(family):
    r, reflect, count = ((0, -1, 1, 0), (1, 0, 0, -1), 4) if family == "omino" else (
        (0, -1, 1, 1), (1, 1, 0, -1), 6)
    power = (1, 0, 0, 1)
    result = []
    for _ in range(count):
        result.extend((power, matmul(power, reflect)))
        power = matmul(r, power)
    return result


def normalize(family, patch):
    x, y = min(patch)
    # Triangular-grid translations preserve colour: only 3Z² is allowed.
    if family == "iamond":
        x, y = 3*(x//3), 3*(y//3)
    return tuple(sorted((a-x, b-y) for a, b in patch))


def orientations(family, shape):
    result = set()
    for m in matrices(family):
        ux, uy = (0, 0)
        if family == "iamond":
            a, b = transform(m, (2, 2))
            ux, uy = (2-a) % 3, (2-b) % 3
        image = {(a+ux, b+uy) for a, b in (transform(m, c) for c in shape)}
        require(all(valid_cell(family, c) for c in image), "isometry left lattice")
        result.add(normalize(family, image))
    return result


def check_witness(family, shape, witness, values):
    require(type(witness) is dict, "witness must be object")
    k = witness.get("k")
    require(integer(k) and k >= 0, "invalid k")
    serves = witness.get("serves")
    require(type(serves) is list and len(serves) > 0 and
            set(serves) <= {"Hc", "Hh"} and len(set(serves)) == len(serves), "invalid serves")
    for mode in serves:
        require(k == values[mode], "k/value mismatch: "+mode)
    tiles = witness.get("tiles")
    require(type(tiles) is list and len(tiles) > 0, "no tiles")
    shapes = orientations(family, shape)
    layers = [[] for _ in range(k+1)]
    used = set()
    for item in tiles:
        require(type(item) is list and len(item) == 2, "invalid tile")
        j, raw = item
        require(integer(j) and 0 <= j <= k, "layer out of range")
        tile = cells(raw, family)
        require(normalize(family, tile) in shapes, "noncongruent tile")
        require(not used.intersection(tile), "P1 overlap")
        used.update(tile)
        layers[j].append(tile)
    require(len(layers[0]) == 1 and layers[0][0] == shape, "P0 origin tile")
    require(all(layers[j] for j in range(1, k+1)), "empty layer")
    patch = set(shape)
    checks = []
    for j in range(k+1):
        details = disk_details(family, patch)
        required = j < k or "Hc" in serves
        require(not required or details["disk"], "D non-disk at layer "+str(j))
        checks.append(dict(layer=j, required=required, **details))
        if j == k:
            break
        boundary = halo(family, patch)
        new = set().union(*layers[j+1])
        require(boundary <= new, "P2 uncovered halo at layer "+str(j))
        require(all(tile.intersection(boundary) for tile in layers[j+1]), "P3 detached tile")
        patch.update(new)
    return {"k": k, "serves": serves, "tiles": len(tiles), "cells": len(used), "layers": checks}


def check_row(row, reference=None):
    family = row.get("family")
    require(family in ("omino", "hex", "iamond"), "invalid family")
    require(integer(row.get("index")) and row["index"] >= 0, "invalid index")
    shape = cells(row.get("shape"), family)
    require(disk_details(family, shape)["disk"], "base shape not disk")
    for mode in ("Hc", "Hh"):
        require(integer(row.get(mode)) and row[mode] >= 0, "invalid value")
    require(row["Hc"] <= row["Hh"] <= row["Hc"]+1, "invalid Hc/Hh relation")
    if reference is not None:
        require(shape == reference["shape"], "public shape/index mismatch")
        require(all(row[m] == reference[m] for m in ("Hc", "Hh")), "public table value mismatch")
    require(type(row.get("witnesses")) is list and row["witnesses"], "no witnesses")
    checked = [check_witness(family, shape, w, row) for w in row["witnesses"]]
    require(set().union(*(set(w["serves"]) for w in checked)) == {"Hc", "Hh"}, "missing mode witness")
    return {"family": family, "file": row.get("file"), "index": row["index"],
            "Hc": row["Hc"], "Hh": row["Hh"], "status": "PASS", "witnesses": checked}
