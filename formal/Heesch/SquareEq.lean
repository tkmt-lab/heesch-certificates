import Heesch.Spec
import Heesch.Square.Ord

/-!
# Heesch CNF soundness on three grids: the square instance is the earlier polyomino encoding

`cnfOrd_square`: the generic `cnfOrd squareGrid ord S K blocks` of
`Heesch.Challenge` equals the earlier polyomino `HeeschSquareProof.cnfOrd ord S K`
(of `Heesch.Square.Ord`, built on the earlier statement `Heesch.Square.Challenge`), with
the hole blocks converted field by field. So the file comparison for the 2,076 square CNFs (made
against the earlier `cnfOrd`) applies to the generic definition unchanged.
-/

namespace HeeschProof
open Heesch

theorem fm_some {α β : Type} (f : α → β) (l : List α) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l <;> simp [*]

theorem cellsLe_square : cellsLe = HeeschSquare.cellsLe := by
  funext a b
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [cellsLe, HeeschSquare.cellsLe, ih]
      rfl

theorem touchingCopies_square :
    touchingCopies squareGrid = HeeschSquare.touchingCopies := by
  funext T0 R
  unfold touchingCopies HeeschSquare.touchingCopies
  have : ∀ (m : Orient) (r s : Cell),
      (squareGrid.nbrs r).filterMap (fun q =>
        if squareGrid.transOk m (q.1 - (applyM m s).1, q.2 - (applyM m s).2) = true then
          some (sortCells (T0.map (place m (q.1 - (applyM m s).1, q.2 - (applyM m s).2))))
        else none) =
      HeeschSquare.nbr8.map fun δ =>
        HeeschSquare.sortCells (T0.map (HeeschSquare.place m
          (r.1 + δ.1 - (HeeschSquare.applyM m s).1,
           r.2 + δ.2 - (HeeschSquare.applyM m s).2))) := by
    intro m r s
    simp only [squareGrid, ite_true, List.filterMap_map]
    exact fm_some _ _
  simp only [this, cellsLe_square]
  rfl

theorem firstReach_square (T0 : List Cell) (K : ℕ) :
    firstReach squareGrid T0 K = HeeschSquare.firstReach T0 K := by
  funext j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [firstReach, HeeschSquare.firstReach, ih, touchingCopies_square]
    rfl

theorem firstLayers_square :
    firstLayers squareGrid = HeeschSquare.firstLayers := by
  funext T0 K
  simp only [firstLayers, HeeschSquare.firstLayers, firstReach_square,
    touchingCopies_square]
  rfl

theorem refine_square : refine squareGrid = HeeschSquare.refine := rfl

theorem fixLayers_square (T0 : List Cell) (K : ℕ) :
    fixLayers squareGrid T0 K = HeeschSquare.fixLayers T0 K := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext Λ
    simp only [fixLayers, HeeschSquare.fixLayers, ih, refine_square]

theorem candidates_square :
    candidates squareGrid = HeeschSquare.candidates := by
  funext S K
  simp only [candidates, HeeschSquare.candidates, firstLayers_square, fixLayers_square]
  rfl

/-- The old polyomino hole block of a new one. -/
def HoleBlock.toOld (b : HoleBlock) : HeeschSquare.HoleBlock :=
  ⟨b.level, b.hole, b.enclosing⟩

theorem posOf_eq {α : Type} [DecidableEq α] : @posOf α _ = @HeeschSquare.posOf α _ := by
  funext a l
  induction l with
  | nil => rfl
  | cons b l ih => simp only [posOf, HeeschSquare.posOf, ih]

theorem amoClauses_eq : amoClauses = HeeschSquare.amoClauses := rfl
theorem sortCells_eq : sortCells = HeeschSquare.sortCells := rfl
theorem reachOf_eq : reachOf = HeeschSquare.reachOf := rfl
theorem haloL_eq : haloL squareGrid = HeeschSquare.haloL := rfl
theorem meets_eq : meets = HeeschSquare.meets := rfl

/-- **The generic CNF on the square grid is the polyomino CNF of the earlier statement**
(`HeeschSquareProof.cnfOrd`, whose soundness `hh_sound_ord`, `hc_sound_ord` was proved before and
whose DIMACS the file comparison compared with the generator's CNFs). -/
theorem cnfOrd_square (ord : Cell → List ℤ → List ℤ) (S : List Cell) (K : ℕ)
    (blocks : List HoleBlock) :
    cnfOrd squareGrid ord S K blocks = HeeschSquareProof.cnfOrd ord S K (blocks.map HoleBlock.toOld) := by
  unfold cnfOrd
  simp only [candidates_square, posOf_eq, amoClauses_eq, sortCells_eq, reachOf_eq, haloL_eq,
    meets_eq]
  conv_rhs => rw [HeeschSquareProof.cnfOrd, HeeschSquareProof.hClH, List.filterMap_map]
  rfl

end HeeschProof
