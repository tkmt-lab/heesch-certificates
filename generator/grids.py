"""The ambient grids: squares (polyominoes), hexagons (polyhexes), triangles (polyiamonds).

A cell is stored as one Python int  key = (x + OFF) * W + (y + OFF)  so that sets of
cells are cheap.  Coordinates are the ones used in Kaplan's data files.

For each grid:
  NBR   offsets of the "touch" neighbourhood (cells sharing at least one point);
        Halo(X) = {c valid, c not in X, c has a NBR-neighbour in X}
  EDGE  offsets of the edge neighbourhood (used only to find holes)
  maps  the point group: (a, b, c, d, ux, uy) for (x, y) -> (a x + b y + ux, c x + d y + uy)
  step  translations allowed: integer vectors (step 1) or vectors in 3Z^2 (iamonds)
  valid(x, y)  whether (x, y) is a cell of the grid (all points for squares/hexagons)
For iamonds (Kaplan 2022, sec. 4.2) the cells live on a sparse subset of the hexagonal
coordinates: "black" triangles at (x, y) with x = y = 0 (mod 3) and "grey" ones at
x = y = 1 (mod 3).  Points with x = y = 2 (mod 3) are the triangle vertices.
NBR and EDGE are given as one union of offsets; an offset that leads to a non-cell is
simply ignored (filtering by valid), which gives the right neighbours for both colours.
"""

W = 1 << 12
OFF = 1 << 11
K00 = OFF * W + OFF


def key(x, y):
    return (x + OFF) * W + (y + OFF)


def unkey(k):
    return (k // W - OFF, k % W - OFF)


def unoff(o):
    """offset int -> (dx, dy)"""
    return unkey(o + K00)


class Grid:
    name = None
    nbr_xy = ()
    edge_xy = ()
    maps = ()
    step = 1
    hole_margin = 2
    all_valid = True

    def __init__(self):
        self.NBR = tuple(dx * W + dy for dx, dy in self.nbr_xy)
        self.EDGE = tuple(dx * W + dy for dx, dy in self.edge_xy)
        self.valid_key = None if self.all_valid else (lambda k: self.valid(*unkey(k)))

    def valid(self, x, y):
        return True

    def normalise(self, cells_xy):
        """Translate (by an allowed vector) to a canonical position."""
        mx, my = min(cells_xy)
        s = self.step
        mx, my = s * (mx // s), s * (my // s)
        return tuple(sorted((x - mx, y - my) for x, y in cells_xy))

    def orientations(self, cells_xy):
        out = set()
        for a, b, c, d, ux, uy in self.maps:
            out.add(self.normalise([(a * x + b * y + ux, c * x + d * y + uy) for x, y in cells_xy]))
        return sorted(out)

    def translation_ok(self, dx, dy):
        return dx % self.step == 0 and dy % self.step == 0

    def halo_off(self, offs):
        """Halo of a set of cells given as offsets relative to a valid position."""
        s = set(offs)
        h = {c + d for c in s for d in self.NBR} - s
        if not self.all_valid:
            h = {c for c in h if self.valid(*unoff(c))}
        return h

    def halo(self, cells):
        s = set(cells)
        h = {c + d for c in s for d in self.NBR} - s
        if not self.all_valid:
            h = {c for c in h if self.valid_key(c)}
        return h


def _lin(mats):
    return tuple((a, b, c, d, 0, 0) for a, b, c, d in mats)


class SquareGrid(Grid):
    name = 'omino'
    nbr_xy = tuple((dx, dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if (dx, dy) != (0, 0))
    edge_xy = ((1, 0), (-1, 0), (0, 1), (0, -1))
    maps = _lin(((1, 0, 0, 1), (0, -1, 1, 0), (-1, 0, 0, -1), (0, 1, -1, 0),
                 (-1, 0, 0, 1), (1, 0, 0, -1), (0, 1, 1, 0), (0, -1, -1, 0)))


def _mul(m, n):
    a, b, c, d = m; e, f, g, h = n
    return (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)


def hex_mats():
    """A = rotation by 60 degrees, B = reflection in the v axis (Kaplan 2022, sec. 4.1),
    in the basis v = (1, 0), w = (1/2, sqrt(3)/2)."""
    A = (0, -1, 1, 1); B = (1, 1, 0, -1)
    out = []
    R = (1, 0, 0, 1)
    for i in range(6):
        out.append(R); out.append(_mul(R, B))
        R = _mul(A, R)
    assert len(set(out)) == 12
    return out


class HexGrid(Grid):
    name = 'hex'
    nbr_xy = ((1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1))
    edge_xy = nbr_xy
    maps = _lin(hex_mats())


# triangles: vertices of the black cell at (0,0) and of the grey cell at (1,1) (offsets)
TRI_V_BLACK = ((-1, 2), (-1, -1), (2, -1))
TRI_V_GREY = ((1, -2), (1, 1), (-2, 1))


def tri_valid(x, y):
    return (x - y) % 3 == 0 and x % 3 in (0, 1)


def tri_vertices(x, y):
    vs = TRI_V_BLACK if x % 3 == 0 else TRI_V_GREY
    return frozenset((x + a, y + b) for a, b in vs)


def _tri_tables():
    nbr, edge = set(), set()
    for cx, cy in ((0, 0), (1, 1)):
        V = tri_vertices(cx, cy)
        for x in range(cx - 6, cx + 7):
            for y in range(cy - 6, cy + 7):
                if (x, y) == (cx, cy) or not tri_valid(x, y):
                    continue
                s = len(V & tri_vertices(x, y))
                if s >= 1:
                    nbr.add((x - cx, y - cy))
                if s == 2:
                    edge.add((x - cx, y - cy))
    maps = []
    for a, b, c, d in hex_mats():
        found = None
        for ux in range(-3, 4):
            for uy in range(-3, 4):
                ok = True
                for cx, cy in ((0, 0), (1, 1)):
                    ix, iy = a * cx + b * cy + ux, c * cx + d * cy + uy
                    if not tri_valid(ix, iy):
                        ok = False; break
                    img = frozenset((a * x + b * y + ux, c * x + d * y + uy) for x, y in tri_vertices(cx, cy))
                    if img != tri_vertices(ix, iy):
                        ok = False; break
                if ok:
                    found = (ux, uy); break
            if found:
                break
        assert found, (a, b, c, d)
        maps.append((a, b, c, d) + found)
    return tuple(sorted(nbr)), tuple(sorted(edge)), tuple(maps)


class IamondGrid(Grid):
    name = 'iamond'
    nbr_xy, edge_xy, maps = _tri_tables()
    step = 3
    hole_margin = 6
    all_valid = False

    def valid(self, x, y):
        return tri_valid(x, y)


GRIDS = {'omino': SquareGrid, 'hex': HexGrid, 'iamond': IamondGrid}


def halo_keys(cells, NBR):
    s = set(cells)
    return {c + d for c in s for d in NBR} - s


def holes_keys(occ, EDGE, valid_key=None, margin=2):
    """Holes of occ: components (under EDGE adjacency) of the complement of occ that lie
    entirely inside the bounding box of occ.  A component with a cell outside that box is
    unbounded.  The components are computed inside the box enlarged by `margin`.
    Returns a list of sets of keys, sorted by smallest key."""
    xs = [c // W for c in occ]; ys = [c % W for c in occ]
    bx0, bx1, by0, by1 = min(xs), max(xs), min(ys), max(ys)
    x0, x1, y0, y1 = bx0 - margin, bx1 + margin, by0 - margin, by1 + margin
    box = set()
    for x in range(x0, x1 + 1):
        base = x * W
        for y in range(y0, y1 + 1):
            k = base + y
            if k not in occ and (valid_key is None or valid_key(k)):
                box.add(k)
    out = []
    while box:
        st = [box.pop()]; comp = set(st)
        while st:
            c = st.pop()
            for d in EDGE:
                n = c + d
                if n in box:
                    box.discard(n); comp.add(n); st.append(n)
        if all(bx0 <= c // W <= bx1 and by0 <= c % W <= by1 for c in comp):
            out.append(comp)
    out.sort(key=lambda h: min(h))
    return out
