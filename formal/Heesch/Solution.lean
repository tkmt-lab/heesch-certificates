import Heesch.Spec
import Heesch.Inst

/-! Solution module for `lake comparator`: proves the six challenge theorems of
`Heesch/Challenge.lean` (soundness on the square, hexagon and
triangle grids). The definitions come from `Heesch.Spec` (the challenge's
namespace up to `cnf`, copied character for character); below is the rest of the challenge's
namespace, with only the six proof lines changed.

Proof (2026-10-22): the polyomino proof of `Heesch.Square.Solution`, made generic
over the grid (`HeeschProof.hh_sound_grid`, `HeeschProof.hc_sound_grid`, for every grid
satisfying `HeeschProof.GridOK`), and the grid facts for the three grids
(`HeeschProof.squareOK`, `HeeschProof.hexOK`, `HeeschProof.triOK`). -/

namespace Heesch

/-! ## 10. The claims -/

/-- **Hh soundness, square grid**: if the CNF (with any order of the counter inputs and any valid
hole blocks of levels `1..K-1`) is unsatisfiable, `S` has no `K`-layer corona in the Hh sense. -/
theorem hh_sound_square (ord : Cell → List ℤ → List ℤ) (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K : ℕ) (hK : 1 ≤ K) (blocks : List HoleBlock)
    (hblocks : ∀ b ∈ blocks, b.Valid squareGrid (K - 1))
    (hunsat : ¬ Satisfiable (cnfOrd squareGrid ord S K blocks)) :
    ¬ ∃ tiles : Tiles, IsCoronaHh squareGrid S.toFinset K tiles := by
  exact HeeschProof.hh_sound_grid HeeschProof.squareOK ord hord S K blocks hblocks hunsat

/-- **Hc soundness, square grid** (valid hole blocks of levels `1..K`). -/
theorem hc_sound_square (ord : Cell → List ℤ → List ℤ) (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K : ℕ) (hK : 1 ≤ K) (blocks : List HoleBlock)
    (hblocks : ∀ b ∈ blocks, b.Valid squareGrid K)
    (hunsat : ¬ Satisfiable (cnfOrd squareGrid ord S K blocks)) :
    ¬ ∃ tiles : Tiles, IsCoronaHc squareGrid S.toFinset K tiles := by
  exact HeeschProof.hc_sound_grid HeeschProof.squareOK ord hord S K blocks hblocks hunsat

/-- **Hh soundness, hexagon grid.** -/
theorem hh_sound_hex (ord : Cell → List ℤ → List ℤ) (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K : ℕ) (hK : 1 ≤ K) (blocks : List HoleBlock)
    (hblocks : ∀ b ∈ blocks, b.Valid hexGrid (K - 1))
    (hunsat : ¬ Satisfiable (cnfOrd hexGrid ord S K blocks)) :
    ¬ ∃ tiles : Tiles, IsCoronaHh hexGrid S.toFinset K tiles := by
  exact HeeschProof.hh_sound_grid HeeschProof.hexOK ord hord S K blocks hblocks hunsat

/-- **Hc soundness, hexagon grid.** -/
theorem hc_sound_hex (ord : Cell → List ℤ → List ℤ) (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K : ℕ) (hK : 1 ≤ K) (blocks : List HoleBlock)
    (hblocks : ∀ b ∈ blocks, b.Valid hexGrid K)
    (hunsat : ¬ Satisfiable (cnfOrd hexGrid ord S K blocks)) :
    ¬ ∃ tiles : Tiles, IsCoronaHc hexGrid S.toFinset K tiles := by
  exact HeeschProof.hc_sound_grid HeeschProof.hexOK ord hord S K blocks hblocks hunsat

/-- **Hh soundness, triangle grid.** -/
theorem hh_sound_tri (ord : Cell → List ℤ → List ℤ) (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K : ℕ) (hK : 1 ≤ K) (blocks : List HoleBlock)
    (hblocks : ∀ b ∈ blocks, b.Valid triGrid (K - 1))
    (hunsat : ¬ Satisfiable (cnfOrd triGrid ord S K blocks)) :
    ¬ ∃ tiles : Tiles, IsCoronaHh triGrid S.toFinset K tiles := by
  exact HeeschProof.hh_sound_grid HeeschProof.triOK ord hord S K blocks hblocks hunsat

/-- **Hc soundness, triangle grid.** -/
theorem hc_sound_tri (ord : Cell → List ℤ → List ℤ) (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K : ℕ) (hK : 1 ≤ K) (blocks : List HoleBlock)
    (hblocks : ∀ b ∈ blocks, b.Valid triGrid K)
    (hunsat : ¬ Satisfiable (cnfOrd triGrid ord S K blocks)) :
    ¬ ∃ tiles : Tiles, IsCoronaHc triGrid S.toFinset K tiles := by
  exact HeeschProof.hc_sound_grid HeeschProof.triOK ord hord S K blocks hblocks hunsat

end Heesch
