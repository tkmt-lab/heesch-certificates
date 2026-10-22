import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Finite.Basic

/-!
# Specification for the Heesch CNF soundness (polyominoes)

The definitions of `Heesch/Square/Challenge.lean` (lines 62–371: from
`namespace HeeschSquare` up to `cnfHc`), copied character for character, so that the
proof modules can import them. Together with the `namespace HeeschSquare` part of
`Heesch/Square/Solution.lean` (the claims, section 6) this is the challenge's
namespace with only the two proof lines changed.
-/

namespace HeeschSquare

/-! ## 1. Geometry (FORMAT.md §1) -/

/-- A cell `(x, y)`: the unit square `[x, x+1] × [y, y+1]`. -/
abbrev Cell := ℤ × ℤ

/-- An orientation `(a, b, c, d)`, acting by `(x, y) ↦ (a x + b y, c x + d y)`. -/
abbrev Orient := ℤ × ℤ × ℤ × ℤ

/-- The eight orientations: four rotations, then four reflections. -/
def orientations : List Orient :=
  [(1, 0, 0, 1), (0, -1, 1, 0), (-1, 0, 0, -1), (0, 1, -1, 0),
   (1, 0, 0, -1), (-1, 0, 0, 1), (0, 1, 1, 0), (0, -1, -1, 0)]

/-- The matrix `m` applied to a cell. -/
def applyM (m : Orient) (c : Cell) : Cell :=
  (m.1 * c.1 + m.2.1 * c.2, m.2.2.1 * c.1 + m.2.2.2 * c.2)

/-- `c ↦ M c + v`. -/
def place (m : Orient) (v : Cell) (c : Cell) : Cell :=
  ((applyM m c).1 + v.1, (applyM m c).2 + v.2)

/-- `T` is a congruent copy `M·S + v` of `S`. -/
def IsCopy (S T : Finset Cell) : Prop :=
  ∃ m ∈ orientations, ∃ v : Cell, T = S.image (place m v)

/-- `d ∈ N8(c)`: a different cell sharing at least a point with `c`. -/
def Touch (c d : Cell) : Prop := c ≠ d ∧ |c.1 - d.1| ≤ 1 ∧ |c.2 - d.2| ≤ 1

/-- `d ∈ N4(c)`: a cell sharing an edge with `c`. -/
def EdgeAdj (c d : Cell) : Prop := |c.1 - d.1| + |c.2 - d.2| = 1

/-- `Halo(X) = { c ∉ X : N8(c) ∩ X ≠ ∅ }`. -/
def halo (X : Set Cell) : Set Cell := {c | c ∉ X ∧ ∃ d ∈ X, Touch c d}

/-- The `N4` grid graph on all cells. -/
def edgeGraph : SimpleGraph Cell := SimpleGraph.fromRel EdgeAdj

/-- `c ∉ P` lies in a hole of `P`: its `N4`-component in the complement of `P` is bounded
(for sets of cells, bounded = finite). -/
def InHole (P : Set Cell) (c : Cell) : Prop :=
  ∃ hc : c ∈ Pᶜ, {d : ↥(Pᶜ) | (edgeGraph.induce Pᶜ).Reachable ⟨c, hc⟩ d}.Finite

/-- `P` has a hole. -/
def HasHole (P : Set Cell) : Prop := ∃ c, InHole P c

/-- At the lattice point `(x, y)`, of the four cells around it
`(x-1,y-1), (x,y-1), (x-1,y), (x,y)`, exactly two diagonally opposite ones lie in `P`. -/
def DiagonalVertex (P : Set Cell) (x y : ℤ) : Prop :=
  ((x - 1, y - 1) ∈ P ∧ (x, y) ∈ P ∧ (x, y - 1) ∉ P ∧ (x - 1, y) ∉ P) ∨
  ((x, y - 1) ∈ P ∧ (x - 1, y) ∈ P ∧ (x - 1, y - 1) ∉ P ∧ (x, y) ∉ P)

/-- The union of the cells `P` is a closed disc: (a) `N4`-connected, (b) no hole,
(c) no vertex touched only diagonally. -/
def IsDisc (P : Set Cell) : Prop :=
  (edgeGraph.induce P).Connected ∧ ¬ HasHole P ∧ ∀ x y : ℤ, ¬ DiagonalVertex P x y

/-- A finite set of tiles, each with its layer number. -/
abbrev Tiles := Finset (ℕ × Finset Cell)

/-- `P_j`: the union of the tiles of layer `≤ j`. -/
def cover (tiles : Tiles) (j : ℕ) : Set Cell := {c | ∃ t ∈ tiles, t.1 ≤ j ∧ c ∈ t.2}

/-- A `k`-layer corona of `S` without the disc condition (D): (P0)–(P3). -/
def IsCorona (S : Finset Cell) (k : ℕ) (tiles : Tiles) : Prop :=
  -- every tile is a congruent copy of `S` with layer in `0..k`
  (∀ t ∈ tiles, t.1 ≤ k ∧ IsCopy S t.2) ∧
  -- (P0) layer 0 is exactly `S` itself, once
  ((0, S) ∈ tiles ∧ ∀ t ∈ tiles, t.1 = 0 → t.2 = S) ∧
  -- (P1) distinct tiles do not overlap
  (∀ t ∈ tiles, ∀ u ∈ tiles, t ≠ u → Disjoint t.2 u.2) ∧
  -- (P2) `Halo(P_j) ⊆ P_{j+1}` for `j < k`
  (∀ j < k, halo (cover tiles j) ⊆ cover tiles (j + 1)) ∧
  -- (P3) a tile of layer `j ≥ 1` has a cell in `Halo(P_{j-1})`
  (∀ t ∈ tiles, 1 ≤ t.1 → ∃ c ∈ t.2, c ∈ halo (cover tiles (t.1 - 1)))

/-- A `k`-layer corona in the Hh sense: `P_0, …, P_{k-1}` are discs (`P_k` may have holes). -/
def IsCoronaHh (S : Finset Cell) (k : ℕ) (tiles : Tiles) : Prop :=
  IsCorona S k tiles ∧ ∀ j < k, IsDisc (cover tiles j)

/-- A `k`-layer corona in the Hc sense: `P_0, …, P_k` are discs. -/
def IsCoronaHc (S : Finset Cell) (k : ℕ) (tiles : Tiles) : Prop :=
  IsCorona S k tiles ∧ ∀ j ≤ k, IsDisc (cover tiles j)

/-! ## 2. CNF and satisfiability -/

/-- A CNF in DIMACS style: a clause is a list of nonzero integer literals. -/
abbrev CNF := List (List ℤ)

/-- Literal `l` is true under `σ` (`0` is never true). -/
def LitTrue (σ : ℕ → Bool) (l : ℤ) : Prop :=
  (0 < l ∧ σ l.natAbs = true) ∨ (l < 0 ∧ σ l.natAbs = false)

/-- Propositional satisfiability. -/
def Satisfiable (F : CNF) : Prop := ∃ σ : ℕ → Bool, ∀ C ∈ F, ∃ l ∈ C, LitTrue σ l

/-! ## 3. Lists of cells (computable helpers) -/

/-- Lexicographic order on cells. -/
def cellLe (a b : Cell) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 ≤ b.2))

/-- Sorted list of the distinct cells of `l`. -/
def sortCells (l : List Cell) : List Cell := l.dedup.mergeSort cellLe

/-- Lexicographic order on (sorted) cell lists. -/
def cellsLe : List Cell → List Cell → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then cellsLe as bs else cellLe a b

/-- The offsets of `N8`. -/
def nbr8 : List Cell := [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]

/-- `c + δ`. -/
def shift (c δ : Cell) : Cell := (c.1 + δ.1, c.2 + δ.2)

/-- `Halo(X)` for a list of cells, sorted. -/
def haloL (X : List Cell) : List Cell :=
  sortCells ((X.flatMap fun c => nbr8.map (shift c)).filter fun c => decide (c ∉ X))

/-- `A ∩ B ≠ ∅`. -/
def meets (A B : List Cell) : Bool := A.any fun c => decide (c ∈ B)

/-- Integers `a, a+1, …, b`. -/
def intRange (a b : ℤ) : List ℤ := (List.range (b - a + 1).toNat).map fun i => a + i

/-- Chebyshev distance: the distance in the `N8` graph on all cells. -/
def cheb (c t : Cell) : ℕ := max (c.1 - t.1).natAbs (c.2 - t.2).natAbs

/-- `d(c)`: the `N8`-distance from `T0` (`none` if `T0` is empty). -/
def dist (T0 : List Cell) (c : Cell) : Option ℕ := (T0.map (cheb c)).min?

/-- `hi = min(K, min_{c ∈ p} d(c))` (FORMAT.md §4.1, from Lemma A). -/
def hiOf (T0 : List Cell) (K : ℕ) (p : List Cell) : ℕ :=
  min K ((p.filterMap (dist T0)).min?.getD 0)

/-- Position of `a` in a list. -/
def posOf {α : Type} [DecidableEq α] (a : α) : List α → Option ℕ
  | [] => none
  | b :: l => if a = b then some 0 else (posOf a l).map (· + 1)

/-! ## 4. Candidate copies and their layers (FORMAT.md §4.1) -/

/-- All copies `p` of `T0` (as sorted cell lists) with `p ∩ T0 = ∅` and `Halo(p) ∩ R ≠ ∅`,
sorted. Every such copy has a cell `r + δ` (`r ∈ R`, `δ ∈ N8`), which fixes the translation. -/
def touchingCopies (T0 R : List Cell) : List (List Cell) :=
  let raw := orientations.flatMap fun m =>
    R.flatMap fun r => T0.flatMap fun s => nbr8.map fun δ =>
      let q := applyM m s
      let v : Cell := (r.1 + δ.1 - q.1, r.2 + δ.2 - q.2)
      sortCells (T0.map (place m v))
  (raw.dedup.filter fun p => !meets p T0 && meets (haloL p) R).mergeSort cellsLe

/-- First sequential pass: `R_0 = T0`, `R_j = R_{j-1} ∪ ⋃ {p : Halo(p) ∩ R_{j-1} ≠ ∅, j ≤ hi(p)}`. -/
def firstReach (T0 : List Cell) (K : ℕ) : ℕ → List Cell
  | 0 => T0
  | j + 1 =>
    let R := firstReach T0 K j
    sortCells (R ++ ((touchingCopies T0 R).filter fun p => decide (j + 1 ≤ hiOf T0 K p)).flatten)

/-- `Λ` after the first pass: copies touching `R_{K-1}`, each with the layers `j ∈ 1..K` such that
`j ≤ hi(p)` and `Halo(p) ∩ R_{j-1} ≠ ∅` (so `lo` is the first layer that touches). -/
def firstLayers (T0 : List Cell) (K : ℕ) : List (List Cell × List ℕ) :=
  let Rs := (List.range K).map (firstReach T0 K)
  (touchingCopies T0 (firstReach T0 K (K - 1))).map fun p =>
    (p, ((List.range K).map (· + 1)).filter fun j =>
      decide (j ≤ hiOf T0 K p) && meets (haloL p) (Rs.getD (j - 1) []))

/-- `R_j` for a layer assignment `Λ`: `T0` and the cells of the copies allowed at a layer `≤ j`. -/
def reachOf (T0 : List Cell) (Λ : List (List Cell × List ℕ)) (j : ℕ) : List Cell :=
  sortCells (T0 ++ ((Λ.filter fun pl => pl.2.any fun l => decide (l ≤ j)).map Prod.fst).flatten)

/-- One re-filtering step: keep layer `j` of `p` iff `Halo(p) ∩ R_{j-1} ≠ ∅` and
(`j = K` or `Halo(p) \ T0 ⊆ R_{j+1}`), with `R` recomputed from the current `Λ`. -/
def refine (T0 : List Cell) (K : ℕ) (Λ : List (List Cell × List ℕ)) :
    List (List Cell × List ℕ) :=
  let Rs := (List.range (K + 2)).map (reachOf T0 Λ)
  Λ.map fun pl => (pl.1, pl.2.filter fun j =>
    meets (haloL pl.1) (Rs.getD (j - 1) []) &&
      (decide (K ≤ j) ||
        ((haloL pl.1).filter fun c => decide (c ∉ T0)).all fun c => decide (c ∈ Rs.getD (j + 1) [])))

/-- Repeat `refine` until nothing changes (with enough fuel: each change removes a pair). -/
def fixLayers (T0 : List Cell) (K : ℕ) : ℕ → List (List Cell × List ℕ) → List (List Cell × List ℕ)
  | 0, Λ => Λ
  | n + 1, Λ =>
    let Λ' := refine T0 K Λ
    if Λ' = Λ then Λ else fixLayers T0 K n Λ'

/-- The candidate copies `p` with their nonempty lists of allowed layers `Λ(p)`. -/
def candidates (S : List Cell) (K : ℕ) : List (List Cell × List ℕ) :=
  let T0 := sortCells S
  let Λ1 := firstLayers T0 K
  (fixLayers T0 K ((Λ1.map fun pl => pl.2.length).sum + 1) Λ1).filter fun pl => !pl.2.isEmpty

/-! ## 5. The clauses (FORMAT.md §4.2–4.4) -/

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
`1 ≤ j ≤ maxLevel`, `H ≠ ∅`, the enclosing tiles have layer `≤ j`, and `∂H` (edge neighbours of
`H` outside `H`) is covered by the enclosing tiles. -/
def HoleBlock.Valid (b : HoleBlock) (maxLevel : ℕ) : Prop :=
  1 ≤ b.level ∧ b.level ≤ maxLevel ∧ b.hole ≠ [] ∧
  (∀ e ∈ b.enclosing, e.1 ≤ b.level) ∧
  ∀ c ∈ b.hole, ∀ d : Cell, EdgeAdj c d → d ∉ b.hole → ∃ e ∈ b.enclosing, d ∈ e.2

/-- The CNF of FORMAT.md §4.3 for shape `S` and `K` layers, plus the hole clauses (H) of
§4.4 for the given blocks. -/
def cnf (S : List Cell) (K : ℕ) (blocks : List HoleBlock) : CNF :=
  let T0 := sortCells S
  let cands := candidates S K
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
    ((List.range nT).filter fun i => decide (c ∈ (tPairs.getD i ([], 0)).1)).map
      fun i => ((i + 1 : ℕ) : ℤ)
  let auxCounts := groups.map fun g => g.length - 1
  let bases := (List.range groups.length).map fun i => nT + nY + (auxCounts.take i).sum
  let vBad : ℤ := ((nT + nY + auxCounts.sum + 1 : ℕ) : ℤ)
  -- (F) `y[c, d(c)]` for `1 ≤ d(c) ≤ K`
  let xs := T0.map Prod.fst
  let ys := T0.map Prod.snd
  let box : List Cell :=
    (intRange (xs.min?.getD 0 - K) (xs.max?.getD 0 + K)).flatMap fun a =>
      (intRange (ys.min?.getD 0 - K) (ys.max?.getD 0 + K)).map fun b => (a, b)
  let fCells := box.filter fun c =>
    match dist T0 c with
    | some d => decide (1 ≤ d ∧ d ≤ K)
    | none => false
  let fOk := fCells.filter fun c => decide (c ∈ R ((dist T0 c).getD 0))
  let clF := fOk.map fun c => [y c ((dist T0 c).getD 0)]
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
      ((haloL pj.1).filter fun c => decide (c ∉ T0)).map fun c =>
        [-(t pj.1 pj.2)] ++ (if c ∈ R (pj.2 + 1) then [y c (pj.2 + 1)] else [])
    else []
  -- (E) `j ≥ 2`, `p` not touching `T0`: `t[p,j] → ⋁ { y[c,j-1] : c ∈ Halo(p) }`
  let clE := tPairs.flatMap fun pj =>
    if 2 ≤ pj.2 ∧ meets (haloL pj.1) T0 = false then
      [[-(t pj.1 pj.2)] ++
        ((haloL pj.1).filter fun c => decide (c ∈ R (pj.2 - 1) ∧ c ∉ T0)).map
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

/-- The CNF of a mode-Hh certificate (FORMAT.md §3): base clauses plus (H) for blocks of
levels `1..K-1`. -/
def cnfHh (S : List Cell) (K : ℕ) (blocks : List HoleBlock) : CNF := cnf S K blocks

/-- The CNF of a mode-Hc certificate (FORMAT.md §3): base clauses plus (H) for blocks of
levels `1..K`. -/
def cnfHc (S : List Cell) (K : ℕ) (blocks : List HoleBlock) : CNF := cnf S K blocks

end HeeschSquare
