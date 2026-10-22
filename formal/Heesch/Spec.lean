import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Finite.Basic

/-!
# Specification for the Heesch CNF soundness on three grids

The definitions of `Heesch/Challenge.lean` (from
`namespace Heesch` up to `cnf`), copied character for character, so that the
proof modules can import them. Together with the `namespace Heesch` part of
`Heesch/Solution.lean` (the claims, section 10) this is the
challenge's namespace with only the six proof lines changed.
-/

namespace Heesch

/-! ## 1. Points, matrices, grids -/

/-- An integer point `(x, y)`. On the square grid it is the unit square `[x,x+1] × [y,y+1]`; on the
hexagon grid the hexagon centred at `x·v + y·w` (`v = (1,0)`, `w = (1/2, √3/2)`); on the triangle
grid, a cell is a triangle whose centroid is the point (only some points are cells). -/
abbrev Cell := ℤ × ℤ

/-- A matrix `[[a, b], [c, d]]` as `(a, b, c, d)`, acting by `(x, y) ↦ (a x + b y, c x + d y)`. -/
abbrev Orient := ℤ × ℤ × ℤ × ℤ

/-- The matrix `m` applied to a point. -/
def applyM (m : Orient) (c : Cell) : Cell :=
  (m.1 * c.1 + m.2.1 * c.2, m.2.2.1 * c.1 + m.2.2.2 * c.2)

/-- `c ↦ m c + w`. -/
def place (m : Orient) (w : Cell) (c : Cell) : Cell :=
  ((applyM m c).1 + w.1, (applyM m c).2 + w.2)

/-- A grid: the geometric notions of FORMAT.md §1 / §1.1 (first five fields) and the computable
helpers of the encoding (last three fields). -/
structure Grid where
  /-- The point is a cell. -/
  isCell : Cell → Prop
  /-- `d` touches `c` (shares at least a point, `d ≠ c`): `d ∈ N(c)` of §1. -/
  Touch : Cell → Cell → Prop
  /-- `d` shares an edge with `c` (holes and connectivity). -/
  EdgeAdj : Cell → Cell → Prop
  /-- `P` has a vertex where its cells meet only at that point (disc condition (c)). -/
  Pinch : Set Cell → Prop
  /-- The orientation matrices. -/
  orients : List Orient
  /-- `x ↦ m x + w` is an allowed congruence (for `m ∈ orients`). -/
  transOk : Orient → Cell → Bool
  /-- The cells touching `c` (computable). -/
  nbrs : Cell → List Cell
  /-- `d(c)`, the distance from `T0` in the touching graph (computable; `none` if unreachable). -/
  dist : List Cell → Cell → Option ℕ
  /-- A finite list of points containing every cell `c` with `d(c) ≤ K` (computable). -/
  box : List Cell → ℕ → List Cell

/-! ## 2. Geometry on a grid (FORMAT.md §1) -/

section Geometry

variable (G : Grid)

/-- `T` is a congruent copy `m·S + w` of `S`. -/
def IsCopy (S T : Finset Cell) : Prop :=
  ∃ m ∈ G.orients, ∃ w : Cell, G.transOk m w = true ∧ T = S.image (place m w)

/-- `Halo(X) = { c ∉ X : c touches some cell of X }`. -/
def halo (X : Set Cell) : Set Cell := {c | c ∉ X ∧ ∃ d ∈ X, G.Touch c d}

/-- The edge-neighbour graph on all points. -/
def edgeGraph : SimpleGraph Cell := SimpleGraph.fromRel G.EdgeAdj

/-- The cell `c ∉ P` lies in a hole of `P`: its edge-component in the complement of `P` is
bounded (for sets of lattice points, bounded = finite). -/
def InHole (P : Set Cell) (c : Cell) : Prop :=
  G.isCell c ∧ ∃ hc : c ∈ Pᶜ, {d : ↥(Pᶜ) | ((edgeGraph G).induce Pᶜ).Reachable ⟨c, hc⟩ d}.Finite

/-- `P` has a hole. -/
def HasHole (P : Set Cell) : Prop := ∃ c, InHole G P c

/-- The union of the cells `P` is a closed disc: (a) edge-connected, (b) no hole, (c) no pinch
vertex. -/
def IsDisc (P : Set Cell) : Prop :=
  ((edgeGraph G).induce P).Connected ∧ ¬ HasHole G P ∧ ¬ G.Pinch P

end Geometry

/-- A finite set of tiles, each with its layer number. -/
abbrev Tiles := Finset (ℕ × Finset Cell)

/-- `P_j`: the union of the tiles of layer `≤ j`. -/
def cover (tiles : Tiles) (j : ℕ) : Set Cell := {c | ∃ t ∈ tiles, t.1 ≤ j ∧ c ∈ t.2}

section Corona

variable (G : Grid)

/-- A `k`-layer corona of `S` without the disc condition (D): (P0)–(P3). -/
def IsCorona (S : Finset Cell) (k : ℕ) (tiles : Tiles) : Prop :=
  -- every tile is a congruent copy of `S` with layer in `0..k`
  (∀ t ∈ tiles, t.1 ≤ k ∧ IsCopy G S t.2) ∧
  -- (P0) layer 0 is exactly `S` itself, once
  ((0, S) ∈ tiles ∧ ∀ t ∈ tiles, t.1 = 0 → t.2 = S) ∧
  -- (P1) distinct tiles do not overlap
  (∀ t ∈ tiles, ∀ u ∈ tiles, t ≠ u → Disjoint t.2 u.2) ∧
  -- (P2) `Halo(P_j) ⊆ P_{j+1}` for `j < k`
  (∀ j < k, halo G (cover tiles j) ⊆ cover tiles (j + 1)) ∧
  -- (P3) a tile of layer `j ≥ 1` has a cell in `Halo(P_{j-1})`
  (∀ t ∈ tiles, 1 ≤ t.1 → ∃ c ∈ t.2, c ∈ halo G (cover tiles (t.1 - 1)))

/-- A `k`-layer corona in the Hh sense: `P_0, …, P_{k-1}` are discs (`P_k` may have holes). -/
def IsCoronaHh (S : Finset Cell) (k : ℕ) (tiles : Tiles) : Prop :=
  IsCorona G S k tiles ∧ ∀ j < k, IsDisc G (cover tiles j)

/-- A `k`-layer corona in the Hc sense: `P_0, …, P_k` are discs. -/
def IsCoronaHc (S : Finset Cell) (k : ℕ) (tiles : Tiles) : Prop :=
  IsCorona G S k tiles ∧ ∀ j ≤ k, IsDisc G (cover tiles j)

end Corona

/-! ## 3. CNF and satisfiability -/

/-- A CNF in DIMACS style: a clause is a list of nonzero integer literals. -/
abbrev CNF := List (List ℤ)

/-- Literal `l` is true under `σ` (`0` is never true). -/
def LitTrue (σ : ℕ → Bool) (l : ℤ) : Prop :=
  (0 < l ∧ σ l.natAbs = true) ∨ (l < 0 ∧ σ l.natAbs = false)

/-- Propositional satisfiability. -/
def Satisfiable (F : CNF) : Prop := ∃ σ : ℕ → Bool, ∀ C ∈ F, ∃ l ∈ C, LitTrue σ l

/-! ## 4. Lists of cells (computable helpers) -/

/-- Lexicographic order on cells. -/
def cellLe (a b : Cell) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))

/-- Sorted list of the distinct cells of `l`. -/
def sortCells (l : List Cell) : List Cell := l.dedup.mergeSort cellLe

/-- Lexicographic order on (sorted) cell lists. -/
def cellsLe : List Cell → List Cell → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then cellsLe as bs else cellLe a b

/-- `c + δ`. -/
def shift (c δ : Cell) : Cell := (c.1 + δ.1, c.2 + δ.2)

/-- `A ∩ B ≠ ∅`. -/
def meets (A B : List Cell) : Bool := A.any fun c => decide (c ∈ B)

/-- Integers `a, a+1, …, b`. -/
def intRange (a b : ℤ) : List ℤ := (List.range (b - a + 1).toNat).map fun i => a + i

/-- The points of the bounding box of `T0`, enlarged by `r` on every side. -/
def boxAround (T0 : List Cell) (r : ℤ) : List Cell :=
  (intRange ((T0.map Prod.fst).min?.getD 0 - r) ((T0.map Prod.fst).max?.getD 0 + r)).flatMap
    fun a => (intRange ((T0.map Prod.snd).min?.getD 0 - r)
      ((T0.map Prod.snd).max?.getD 0 + r)).map fun b => (a, b)

/-- Position of `a` in a list. -/
def posOf {α : Type} [DecidableEq α] (a : α) : List α → Option ℕ
  | [] => none
  | b :: l => if a = b then some 0 else (posOf a l).map (· + 1)

/-! ## 5. The square grid (polyominoes, FORMAT.md §1) -/

/-- The eight orientations: four rotations, then four reflections. -/
def squareOrients : List Orient :=
  [(1, 0, 0, 1), (0, -1, 1, 0), (-1, 0, 0, -1), (0, 1, -1, 0),
   (1, 0, 0, -1), (-1, 0, 0, 1), (0, 1, 1, 0), (0, -1, -1, 0)]

/-- `d ∈ N8(c)`: a different cell sharing at least a point with `c`. -/
def squareTouch (c d : Cell) : Prop := c ≠ d ∧ |c.1 - d.1| ≤ 1 ∧ |c.2 - d.2| ≤ 1

/-- `d ∈ N4(c)`: a cell sharing an edge with `c`. -/
def squareEdgeAdj (c d : Cell) : Prop := |c.1 - d.1| + |c.2 - d.2| = 1

/-- At the lattice point `(x, y)`, of the four cells around it
`(x-1,y-1), (x,y-1), (x-1,y), (x,y)`, exactly two diagonally opposite ones lie in `P`. -/
def DiagonalVertex (P : Set Cell) (x y : ℤ) : Prop :=
  ((x - 1, y - 1) ∈ P ∧ (x, y) ∈ P ∧ (x, y - 1) ∉ P ∧ (x - 1, y) ∉ P) ∨
  ((x, y - 1) ∈ P ∧ (x - 1, y) ∈ P ∧ (x - 1, y - 1) ∉ P ∧ (x, y) ∉ P)

/-- The offsets of `N8`. -/
def nbr8 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]

/-- Chebyshev distance: the distance in the `N8` graph on all cells. -/
def cheb (c t : Cell) : ℕ := max (c.1 - t.1).natAbs (c.2 - t.2).natAbs

/-- The square grid. -/
def squareGrid : Grid where
  isCell := fun _ => True
  Touch := squareTouch
  EdgeAdj := squareEdgeAdj
  Pinch := fun P => ∃ x y : ℤ, DiagonalVertex P x y
  orients := squareOrients
  transOk := fun _ _ => true
  nbrs := fun c => nbr8.map (shift c)
  dist := fun T0 c => (T0.map (cheb c)).min?
  box := fun T0 K => boxAround T0 K

/-! ## 6. The hexagon grid (polyhexes, FORMAT.md §1.1) -/

/-- Matrix product `m n`. -/
def mmul (m n : Orient) : Orient :=
  (m.1 * n.1 + m.2.1 * n.2.2.1, m.1 * n.2.1 + m.2.1 * n.2.2.2,
   m.2.2.1 * n.1 + m.2.2.2 * n.2.2.1, m.2.2.1 * n.2.1 + m.2.2.2 * n.2.2.2)

/-- Matrix power `m ^ i`. -/
def mpow (m : Orient) : ℕ → Orient
  | 0 => (1, 0, 0, 1)
  | i + 1 => mmul (mpow m i) m

/-- `A = [[0, -1], [1, 1]]`: rotation by 60°. -/
def hexA : Orient := (0, -1, 1, 1)

/-- `B = [[1, 1], [0, -1]]`: reflection in the `v` axis. -/
def hexB : Orient := (1, 1, 0, -1)

/-- The twelve orientations `A^i B^j` (`0 ≤ i < 6`, `0 ≤ j < 2`). -/
def hexOrients : List Orient := (List.range 6).flatMap fun i => [mpow hexA i, mmul (mpow hexA i) hexB]

/-- The six neighbour offsets `(±1, 0), (0, ±1), (1, -1), (-1, 1)`. -/
def hexOffsets : List Cell := [(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)]

/-- `d` is one of the six hexagons around `c` (touching = sharing an edge). -/
def hexTouch (c d : Cell) : Prop := (d.1 - c.1, d.2 - c.2) ∈ hexOffsets

/-- The hexagon-grid norm `max(|a|, |b|, |a + b|)`: the number of steps along `hexOffsets`. -/
def hexNorm (a : Cell) : ℕ := max (max a.1.natAbs a.2.natAbs) (a.1 + a.2).natAbs

/-- The hexagon grid. -/
def hexGrid : Grid where
  isCell := fun _ => True
  Touch := hexTouch
  EdgeAdj := hexTouch
  Pinch := fun _ => False
  orients := hexOrients
  transOk := fun _ _ => true
  nbrs := fun c => hexOffsets.map (shift c)
  dist := fun T0 c => (T0.map fun t => hexNorm (c.1 - t.1, c.2 - t.2)).min?
  box := fun T0 K => boxAround T0 K

/-! ## 7. The triangle grid (polyiamonds, FORMAT.md §1.1) -/

/-- The point is a triangle: black (`x ≡ y ≡ 0 mod 3`) or grey (`x ≡ y ≡ 1 mod 3`). -/
def triIsCell (c : Cell) : Prop := (c.1 % 3 = 0 ∧ c.2 % 3 = 0) ∨ (c.1 % 3 = 1 ∧ c.2 % 3 = 1)

/-- The three vertices of a triangle (empty for a point that is not a cell). Vertices are the
points with `x ≡ y ≡ 2 mod 3`. -/
def triVerts (c : Cell) : List Cell :=
  if c.1 % 3 = 0 ∧ c.2 % 3 = 0 then [(c.1 - 1, c.2 + 2), (c.1 - 1, c.2 - 1), (c.1 + 2, c.2 - 1)]
  else if c.1 % 3 = 1 ∧ c.2 % 3 = 1 then [(c.1 + 1, c.2 - 2), (c.1 + 1, c.2 + 1), (c.1 - 2, c.2 + 1)]
  else []

/-- Touching: two different triangles sharing at least one vertex. -/
def triTouch (c d : Cell) : Prop := c ≠ d ∧ ∃ v ∈ triVerts c, v ∈ triVerts d

/-- Edge neighbours: two different triangles sharing two different vertices. -/
def triEdgeAdj (c d : Cell) : Prop :=
  c ≠ d ∧ ∃ v ∈ triVerts c, ∃ w ∈ triVerts c, v ≠ w ∧ v ∈ triVerts d ∧ w ∈ triVerts d

/-- The six triangles around the vertex point `z`, in counterclockwise angular order
(black and grey alternate). -/
def triRing (z : Cell) : List Cell :=
  [(z.1 + 1, z.2 + 1), (z.1 - 1, z.2 + 2), (z.1 - 2, z.2 + 1),
   (z.1 - 1, z.2 - 1), (z.1 + 1, z.2 - 2), (z.1 + 2, z.2 - 1)]

/-- Going around `z`, position `i` is not in `P` and the next position (cyclically) is. -/
def TriRise (P : Set Cell) (z : Cell) (i : Fin 6) : Prop :=
  (triRing z).getD i.val (0, 0) ∉ P ∧ (triRing z).getD ((i.val + 1) % 6) (0, 0) ∈ P

/-- A pinch vertex: around the vertex point `z`, the triangles of `P` form at least two separate
runs (equivalently, at least two positions where a run of `P` begins). -/
def triPinch (P : Set Cell) : Prop :=
  ∃ z : Cell, z.1 % 3 = 2 ∧ z.2 % 3 = 2 ∧ ∃ i j : Fin 6, i ≠ j ∧ TriRise P z i ∧ TriRise P z j

/-- `x ↦ m x + w` sends the vertex point `(2, 2)` to a vertex point. For an integer matrix `m`
this holds iff it sends every vertex point (`≡ (2,2) mod 3`) to a vertex point, i.e. iff it maps
the triangle grid onto itself (for the twelve hexagon matrices); these are the maps
`x ↦ M x + u + v`, `v ∈ 3ℤ²`, of FORMAT.md §1.1. -/
def triTransOk (m : Orient) (w : Cell) : Bool :=
  decide (((applyM m (2, 2)).1 + w.1) % 3 = 2 ∧ ((applyM m (2, 2)).2 + w.2) % 3 = 2)

/-- `triIsCell` as a `Bool` (the same condition). -/
def triCellB (c : Cell) : Bool :=
  decide ((c.1 % 3 = 0 ∧ c.2 % 3 = 0) ∨ (c.1 % 3 = 1 ∧ c.2 % 3 = 1))

/-- The triangles touching `c`: all triangles around the vertices of `c`, except `c`. -/
def triNbrs (c : Cell) : List Cell := ((triVerts c).flatMap triRing).filter fun d => decide (d ≠ c)

/-- The distance between two triangles in the touching graph: `0` if equal, otherwise
`1 + min` over vertices `u` of `c` and `u'` of `t` of the distance of `u, u'` in the graph of
vertex points (their difference is in `3ℤ²`, and adjacent vertices differ by three times a
hexagon offset). -/
def triDist1 (c t : Cell) : ℕ :=
  if c = t then 0 else
    1 + (((triVerts c).flatMap fun u => (triVerts t).map fun u' =>
      hexNorm ((u.1 - u'.1) / 3, (u.2 - u'.2) / 3)).min?.getD 0)

/-- The triangle grid. -/
def triGrid : Grid where
  isCell := triIsCell
  Touch := triTouch
  EdgeAdj := triEdgeAdj
  Pinch := triPinch
  orients := hexOrients
  transOk := triTransOk
  nbrs := triNbrs
  dist := fun T0 c => if triCellB c then ((T0.filter triCellB).map (triDist1 c)).min? else none
  box := fun T0 K => boxAround T0 (4 * K)

/-! ## 8. Candidate copies and their layers (FORMAT.md §4.1) -/

section Encoding

variable (G : Grid)

/-- `Halo(X)` for a list of cells, sorted. -/
def haloL (X : List Cell) : List Cell :=
  sortCells ((X.flatMap fun c => G.nbrs c).filter fun c => decide (c ∉ X))

/-- `hi = min(K, min_{c ∈ p} d(c))` (FORMAT.md §4.1, from Lemma A). -/
def hiOf (T0 : List Cell) (K : ℕ) (p : List Cell) : ℕ :=
  min K ((p.filterMap (G.dist T0)).min?.getD 0)

/-- All copies `p` of `T0` (as sorted cell lists) with `p ∩ T0 = ∅` and `Halo(p) ∩ R ≠ ∅`,
sorted. Every such copy has a cell `q` touching some `r ∈ R`, which fixes the translation. -/
def touchingCopies (T0 R : List Cell) : List (List Cell) :=
  let raw := G.orients.flatMap fun m =>
    R.flatMap fun r => T0.flatMap fun s => (G.nbrs r).filterMap fun q =>
      let w : Cell := (q.1 - (applyM m s).1, q.2 - (applyM m s).2)
      if G.transOk m w then some (sortCells (T0.map (place m w))) else none
  (raw.dedup.filter fun p => !meets p T0 && meets (haloL G p) R).mergeSort cellsLe

/-- First sequential pass: `R_0 = T0`,
`R_j = R_{j-1} ∪ ⋃ {p : Halo(p) ∩ R_{j-1} ≠ ∅, j ≤ hi(p)}`. -/
def firstReach (T0 : List Cell) (K : ℕ) : ℕ → List Cell
  | 0 => T0
  | j + 1 =>
    let R := firstReach T0 K j
    sortCells (R ++
      ((touchingCopies G T0 R).filter fun p => decide (j + 1 ≤ hiOf G T0 K p)).flatten)

/-- `Λ` after the first pass: copies touching `R_{K-1}`, each with the layers `j ∈ 1..K` such that
`j ≤ hi(p)` and `Halo(p) ∩ R_{j-1} ≠ ∅` (so `lo` is the first layer that touches). -/
def firstLayers (T0 : List Cell) (K : ℕ) : List (List Cell × List ℕ) :=
  let Rs := (List.range K).map (firstReach G T0 K)
  (touchingCopies G T0 (firstReach G T0 K (K - 1))).map fun p =>
    (p, ((List.range K).map (· + 1)).filter fun j =>
      decide (j ≤ hiOf G T0 K p) && meets (haloL G p) (Rs.getD (j - 1) []))

/-- `R_j` for a layer assignment `Λ`: `T0` and the cells of the copies allowed at a layer `≤ j`. -/
def reachOf (T0 : List Cell) (Λ : List (List Cell × List ℕ)) (j : ℕ) : List Cell :=
  sortCells (T0 ++ ((Λ.filter fun pl => pl.2.any fun l => decide (l ≤ j)).map Prod.fst).flatten)

/-- One re-filtering step: keep layer `j` of `p` iff `Halo(p) ∩ R_{j-1} ≠ ∅` and
(`j = K` or `Halo(p) \ T0 ⊆ R_{j+1}`), with `R` recomputed from the current `Λ`. -/
def refine (T0 : List Cell) (K : ℕ) (Λ : List (List Cell × List ℕ)) :
    List (List Cell × List ℕ) :=
  let Rs := (List.range (K + 2)).map (reachOf T0 Λ)
  Λ.map fun pl => (pl.1, pl.2.filter fun j =>
    meets (haloL G pl.1) (Rs.getD (j - 1) []) &&
      (decide (K ≤ j) ||
        ((haloL G pl.1).filter fun c => decide (c ∉ T0)).all
          fun c => decide (c ∈ Rs.getD (j + 1) [])))

/-- Repeat `refine` until nothing changes (with enough fuel: each change removes a pair). -/
def fixLayers (T0 : List Cell) (K : ℕ) : ℕ → List (List Cell × List ℕ) → List (List Cell × List ℕ)
  | 0, Λ => Λ
  | n + 1, Λ =>
    let Λ' := refine G T0 K Λ
    if Λ' = Λ then Λ else fixLayers T0 K n Λ'

/-- The candidate copies `p` with their nonempty lists of allowed layers `Λ(p)`. -/
def candidates (S : List Cell) (K : ℕ) : List (List Cell × List ℕ) :=
  let T0 := sortCells S
  let Λ1 := firstLayers G T0 K
  (fixLayers G T0 K ((Λ1.map fun pl => pl.2.length).sum + 1) Λ1).filter fun pl => !pl.2.isEmpty

end Encoding

/-! ## 9. The clauses (FORMAT.md §4.2–4.4) -/

/-- Sequential "at most one" counter (Sinz 2005) on `x_1..x_m` with counter variables
`s_a = base + a` (`1 ≤ a ≤ m-1`): `x_1 → s_1`; for `1 < a < m`: `x_a → s_a`, `s_{a-1} → s_a`,
`x_a → ¬s_{a-1}`; `x_m → ¬s_{m-1}`. No clause when `m ≤ 1`. -/
def amoClauses (xs : List ℤ) (base : ℕ) : CNF :=
  let m := xs.length
  if m ≤ 1 then [] else
    let x : ℕ → ℤ := fun a => xs.getD (a - 1) 0
    let s : ℕ → ℤ := fun a => ((base + a : ℕ) : ℤ)
    [[-x 1, s 1]] ++
      ((List.range (m - 2)).map (· + 2)).flatMap (fun a =>
        [[-x a, s a], [-s (a - 1), s a], [-x a, -s (a - 1)]]) ++
      [[-x m, -s (m - 1)]]

/-- A hole block (FORMAT.md §4.4, the certificate's `blocks`): level `j`, hole `H`, and the
enclosing tiles `E` as (layer, cells). -/
structure HoleBlock where
  level : ℕ
  hole : List Cell
  enclosing : List (ℕ × List Cell)

/-- What a checker verifies about a block, with `maxLevel = K - 1` (Hh) or `K` (Hc):
`1 ≤ j ≤ maxLevel`, `H ≠ ∅`, every point of `H` is a cell, the enclosing tiles have layer `≤ j`,
and `∂H` (edge neighbours of `H` outside `H`) is covered by the enclosing tiles. -/
def HoleBlock.Valid (G : Grid) (b : HoleBlock) (maxLevel : ℕ) : Prop :=
  1 ≤ b.level ∧ b.level ≤ maxLevel ∧ b.hole ≠ [] ∧ (∀ c ∈ b.hole, G.isCell c) ∧
  (∀ e ∈ b.enclosing, e.1 ≤ b.level) ∧
  ∀ c ∈ b.hole, ∀ d : Cell, G.EdgeAdj c d → d ∉ b.hole → ∃ e ∈ b.enclosing, d ∈ e.2

/-- The CNF of FORMAT.md §4.3 for shape `S` and `K` layers on the grid `G`, plus the hole clauses
(H) of §4.4 for the given blocks; the inputs of the counter of cell `c` are listed in the order
`ord c g`, where `g` is the list of its `t` variables in increasing order. -/
def cnfOrd (G : Grid) (ord : Cell → List ℤ → List ℤ) (S : List Cell) (K : ℕ)
    (blocks : List HoleBlock) : CNF :=
  let T0 := sortCells S
  let cands := candidates G S K
  let Rs := (List.range (K + 2)).map (reachOf T0 cands)
  let R : ℕ → List Cell := fun j => Rs.getD j []
  let layers : List ℕ := (List.range K).map (· + 1)
  -- variables `t[p,j]`, `j ∈ Λ(p)`
  let tPairs : List (List Cell × ℕ) := cands.flatMap fun pl => pl.2.map fun j => (pl.1, j)
  let nT := tPairs.length
  -- variables `y[c,j]`, `c ∈ R_j \ T0`, `1 ≤ j ≤ K`
  let yPairs : List (Cell × ℕ) :=
    layers.flatMap fun j => ((R j).filter fun c => decide (c ∉ T0)).map fun c => (c, j)
  let nY := yPairs.length
  let tVar : List Cell → ℕ → Option ℤ := fun p j =>
    (posOf (p, j) tPairs).map fun i => ((i + 1 : ℕ) : ℤ)
  let yVar : Cell → ℕ → Option ℤ := fun c j =>
    (posOf (c, j) yPairs).map fun i => ((nT + i + 1 : ℕ) : ℤ)
  let t : List Cell → ℕ → ℤ := fun p j => (tVar p j).getD 0
  let y : Cell → ℕ → ℤ := fun c j => (yVar c j).getD 0
  -- (C) groups: for each cell, the `t[p,j]` with `c ∈ p`; counter variables after `t` and `y`
  let coverCells := sortCells (cands.map Prod.fst).flatten
  let groups : List (List ℤ) := coverCells.map fun c =>
    ord c (((List.range nT).filter fun i => decide (c ∈ (tPairs.getD i ([], 0)).1)).map
      fun i => ((i + 1 : ℕ) : ℤ))
  let auxCounts := groups.map fun g => g.length - 1
  let bases := (List.range groups.length).map fun i => nT + nY + (auxCounts.take i).sum
  let vBad : ℤ := ((nT + nY + auxCounts.sum + 1 : ℕ) : ℤ)
  -- (F) `y[c, d(c)]` for `1 ≤ d(c) ≤ K`
  let fCells := (G.box T0 K).filter fun c =>
    match G.dist T0 c with
    | some d => decide (1 ≤ d ∧ d ≤ K)
    | none => false
  let fOk := fCells.filter fun c => decide (c ∈ R ((G.dist T0 c).getD 0))
  let clF := fOk.map fun c => [y c ((G.dist T0 c).getD 0)]
  let clBad : CNF := if fOk.length < fCells.length then [[vBad], [-vBad]] else []
  -- (Y1) `y[c,j-1] → y[c,j]`
  let clY1 := ((List.range (K - 1)).map (· + 2)).flatMap fun j =>
    ((R (j - 1)).filter fun c => decide (c ∉ T0)).map fun c => [-(y c (j - 1)), y c j]
  -- (Y2) `y[c,j] → y[c,j-1] ∨ ⋁ t[p,j]`
  let clY2 := layers.flatMap fun j =>
    ((R j).filter fun c => decide (c ∉ T0)).map fun c =>
      [-(y c j)] ++ (if 2 ≤ j ∧ c ∈ R (j - 1) then [y c (j - 1)] else []) ++
        ((tPairs.filter fun pj => decide (pj.2 = j ∧ c ∈ pj.1)).map fun pj => t pj.1 pj.2)
  -- (B) `t[p,j] → y[c,j]` for `c ∈ p`
  let clB := tPairs.flatMap fun pj => pj.1.map fun c => [-(t pj.1 pj.2), y c pj.2]
  -- (C) at most one `t[p,j]` per cell
  let clC := (groups.zip bases).flatMap fun gb => amoClauses gb.1 gb.2
  -- (D) `j < K`: `t[p,j] → y[c,j+1]` for `c ∈ Halo(p) \ T0`
  let clD := tPairs.flatMap fun pj =>
    if pj.2 < K then
      ((haloL G pj.1).filter fun c => decide (c ∉ T0)).map fun c =>
        [-(t pj.1 pj.2)] ++ (if c ∈ R (pj.2 + 1) then [y c (pj.2 + 1)] else [])
    else []
  -- (E) `j ≥ 2`, `p` not touching `T0`: `t[p,j] → ⋁ { y[c,j-1] : c ∈ Halo(p) }`
  let clE := tPairs.flatMap fun pj =>
    if 2 ≤ pj.2 ∧ meets (haloL G pj.1) T0 = false then
      [[-(t pj.1 pj.2)] ++
        ((haloL G pj.1).filter fun c => decide (c ∈ R (pj.2 - 1) ∧ c ∉ T0)).map
          fun c => y c (pj.2 - 1)]
    else []
  -- (H) `⋁_{(p,l) ∈ E} ¬t[p,l] ∨ ⋁_{c ∈ H} y[c,j]`
  let clH := blocks.filterMap fun b =>
    let encl := b.enclosing.map fun e => (e.1, sortCells e.2)
    if b.hole.any (fun c => decide (c ∈ T0)) then none
    else if encl.any (fun e => !(decide (e.1 = 0 ∧ e.2 = T0)) && (tVar e.2 e.1).isNone) then none
    else some ((encl.filterMap fun e => (tVar e.2 e.1).map (- ·)) ++
      (sortCells b.hole).filterMap fun c => yVar c b.level)
  clF ++ clBad ++ clY1 ++ clY2 ++ clB ++ clC ++ clD ++ clE ++ clH

/-- The CNF with the counter inputs in increasing order. -/
def cnf (G : Grid) (S : List Cell) (K : ℕ) (blocks : List HoleBlock) : CNF :=
  cnfOrd G (fun _ g => g) S K blocks

end Heesch
