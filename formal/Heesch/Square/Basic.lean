import Heesch.Square.Spec
import Mathlib.Algebra.Order.Group.Abs

/-!
# Heesch CNF soundness (polyominoes), basic list lemmas

Membership lemmas for the computable helpers of `Heesch.Square.Spec` (`sortCells`, `haloL`,
`meets`, `posOf`), the link `Touch ↔ nbr8`, and the uniqueness of sorted cell lists.
-/

namespace HeeschSquareProof

open HeeschSquare

/-! ## The lexicographic order -/

theorem cellLe_trans (a b c : Cell) :
    cellLe a b = true → cellLe b c = true → cellLe a c = true := by
  simp only [cellLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem cellLe_total (a b : Cell) : (cellLe a b || cellLe b a) = true := by
  simp only [cellLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem cellLe_antisymm (a b : Cell) : cellLe a b = true → cellLe b a = true → a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [cellLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq]; omega

/-! ## `sortCells` -/

@[simp] theorem mem_sortCells {c : Cell} {l : List Cell} : c ∈ sortCells l ↔ c ∈ l := by
  simp [sortCells, List.mem_mergeSort, List.mem_dedup]

theorem sortCells_pairwise (l : List Cell) : (sortCells l).Pairwise (fun a b => cellLe a b) :=
  List.pairwise_mergeSort cellLe_trans cellLe_total _

theorem sortCells_nodup (l : List Cell) : (sortCells l).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_dedup l)

theorem sortCells_ext {l l' : List Cell} (h : ∀ c, c ∈ l ↔ c ∈ l') :
    sortCells l = sortCells l' := by
  apply List.Perm.eq_of_pairwise (le := fun a b => cellLe a b)
  · intro a b _ _ h1 h2; exact cellLe_antisymm a b h1 h2
  · exact sortCells_pairwise l
  · exact sortCells_pairwise l'
  · rw [List.perm_ext_iff_of_nodup (sortCells_nodup l) (sortCells_nodup l')]
    intro c; simp [h c]

/-- A list is an output of `sortCells`. -/
def IsSorted (p : List Cell) : Prop := ∃ l, p = sortCells l

theorem IsSorted.eq {p q : List Cell} (hp : IsSorted p) (hq : IsSorted q)
    (h : ∀ c, c ∈ p ↔ c ∈ q) : p = q := by
  obtain ⟨l, rfl⟩ := hp; obtain ⟨l', rfl⟩ := hq
  apply sortCells_ext; intro c; have := h c; simpa using this

/-! ## Neighbours -/

theorem touch_iff {c d : Cell} : Touch c d ↔ ∃ δ ∈ nbr8, c = shift d δ := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
  simp only [Touch, nbr8, shift, List.mem_cons, List.not_mem_nil, or_false, ne_eq,
    Prod.mk.injEq, abs_le, Prod.exists]
  constructor
  · rintro ⟨hne, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨c1 - d1, c2 - d2, ?_, by omega, by omega⟩
    omega
  · rintro ⟨a, b, hδ, rfl, rfl⟩
    omega

theorem touch_symm {c d : Cell} : Touch c d → Touch d c := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
  simp only [Touch, ne_eq, Prod.mk.injEq, abs_le]; omega

theorem edgeAdj_symm {c d : Cell} : EdgeAdj c d → EdgeAdj d c := by
  simp only [EdgeAdj, Int.abs_eq_natAbs]; omega

/-! ## `haloL`, `meets` -/

theorem mem_haloL {c : Cell} {X : List Cell} : c ∈ haloL X ↔ c ∉ X ∧ ∃ d ∈ X, Touch c d := by
  simp only [haloL, mem_sortCells, List.mem_filter, List.mem_flatMap, List.mem_map,
    decide_eq_true_eq, touch_iff]
  constructor
  · rintro ⟨⟨d, hd, δ, hδ, rfl⟩, hc⟩; exact ⟨hc, d, hd, δ, hδ, rfl⟩
  · rintro ⟨hc, d, hd, δ, hδ, rfl⟩; exact ⟨⟨d, hd, δ, hδ, rfl⟩, hc⟩

theorem meets_iff {A B : List Cell} : meets A B = true ↔ ∃ c ∈ A, c ∈ B := by
  simp [meets, List.any_eq_true]

theorem meets_false_iff {A B : List Cell} : meets A B = false ↔ ∀ c ∈ A, c ∉ B := by
  rw [← Bool.not_eq_true, meets_iff]; simp

/-! ## `posOf` -/

theorem posOf_getD {α : Type} [DecidableEq α] {a d : α} :
    ∀ {l : List α} {i : ℕ}, posOf a l = some i → l.getD i d = a
  | [], i, h => by simp [posOf] at h
  | b :: l, i, h => by
    unfold posOf at h
    split_ifs at h with hab
    · cases h; simp [hab]
    · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using posOf_getD hk

theorem posOf_lt {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α} {i : ℕ}, posOf a l = some i → i < l.length
  | [], i, h => by simp [posOf] at h
  | b :: l, i, h => by
    unfold posOf at h
    split_ifs at h with hab
    · cases h; simp
    · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      have := posOf_lt hk; simp; omega

theorem posOf_isSome {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∈ l → ∃ i, posOf a l = some i
  | [], h => by simp at h
  | b :: l, h => by
    unfold posOf
    split_ifs with hab
    · exact ⟨0, rfl⟩
    · have : a ∈ l := by simp [hab] at h; exact h
      obtain ⟨i, hi⟩ := posOf_isSome this
      exact ⟨i + 1, by simp [hi]⟩

theorem posOf_none {α : Type} [DecidableEq α] {a : α} {l : List α} (h : posOf a l = none) :
    a ∉ l := by
  intro ha; obtain ⟨i, hi⟩ := posOf_isSome ha; simp [hi] at h

theorem mem_of_posOf {α : Type} [DecidableEq α] {a : α} {l : List α} {i : ℕ}
    (h : posOf a l = some i) : a ∈ l := by
  have h1 := posOf_lt h
  have h2 : l.getD i a = a := posOf_getD h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at h2
  simp only [Option.getD_some] at h2
  rw [← h2]; exact List.getElem_mem h1

/-! ## Chebyshev distance -/

theorem cheb_le_iff {c t : Cell} {j : ℕ} :
    cheb c t ≤ j ↔ (c.1 - t.1).natAbs ≤ j ∧ (c.2 - t.2).natAbs ≤ j := by
  simp [cheb]

/-- One step towards `t`. -/
theorem cheb_step {c t : Cell} {j : ℕ} (h : cheb c t ≤ j + 1) :
    ∃ c', (c' = c ∨ Touch c c') ∧ cheb c' t ≤ j := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨t1, t2⟩ := t
  rw [cheb_le_iff] at h
  simp only at h
  have key : ∀ a : ℤ, (a - 0).natAbs ≤ j + 1 → ∃ e : ℤ, -1 ≤ e ∧ e ≤ 1 ∧ (a - e).natAbs ≤ j ∧
      (e = 0 → a.natAbs ≤ j) := by
    intro a ha
    rcases lt_trichotomy a 0 with h0 | h0 | h0
    · exact ⟨-1, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, by omega, by omega, by omega, by omega⟩
    · exact ⟨1, by omega, by omega, by omega, by omega⟩
  obtain ⟨e1, he1, he1', h1, _⟩ := key (c1 - t1) (by simpa using h.1)
  obtain ⟨e2, he2, he2', h2, _⟩ := key (c2 - t2) (by simpa using h.2)
  refine ⟨(c1 - e1, c2 - e2), ?_, ?_⟩
  · by_cases he : e1 = 0 ∧ e2 = 0
    · left; simp [he.1, he.2]
    · right
      simp only [Touch, ne_eq, Prod.mk.injEq, abs_le]; omega
  · rw [cheb_le_iff]; simp only; constructor <;> omega

end HeeschSquareProof
