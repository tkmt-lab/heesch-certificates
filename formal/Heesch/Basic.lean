import Heesch.Spec
import Mathlib.Algebra.Order.Group.Abs

/-!
# Heesch CNF soundness on three grids: basic lemmas and properties of a corona

The grid-dependent facts used by the soundness proof are collected in `GridOK G` (proved for the
three grids in `Heesch.Inst`). From them: membership lemmas for the computable helpers
(`sortCells`, `haloL`, `meets`, `posOf`), uniqueness of sorted cell lists, and the properties of a
corona (`P_0 = S`, Lemma A from the one-step property of the distance, halo facts, the hole
lemma). This is `Heesch.Square.Basic` and `Heesch.Square.Geom` made generic over the grid.
-/

namespace HeeschProof

open Heesch

/-- The grid-dependent facts used by the proof. -/
structure GridOK (G : Grid) : Prop where
  touch_iff : ∀ c d, G.Touch c d ↔ c ∈ G.nbrs d
  touch_symm : ∀ c d, G.Touch c d → G.Touch d c
  touch_cell : ∀ c d, G.Touch c d → G.isCell c
  edge_symm : ∀ c d, G.EdgeAdj c d → G.EdgeAdj d c
  dist_zero : ∀ T0 c, G.dist T0 c = some 0 → c ∈ T0
  dist_step : ∀ T0 c n, G.dist T0 c = some (n + 1) →
    ∃ c', G.Touch c c' ∧ ∃ m, m ≤ n ∧ G.dist T0 c' = some m
  dist_mem : ∀ T0 c d, c ∈ T0 → G.dist T0 c = some d → d = 0
  dist_some : ∀ T0 c, G.isCell c → (∃ t ∈ T0, G.isCell t) → G.dist T0 c ≠ none
  copy_cell : ∀ m ∈ G.orients, ∀ w, G.transOk m w = true → ∀ x,
    G.isCell (place m w x) → G.isCell x

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

/-! ## `haloL`, `meets` -/

variable {G : Grid}

theorem mem_haloL (hG : GridOK G) {c : Cell} {X : List Cell} :
    c ∈ haloL G X ↔ c ∉ X ∧ ∃ d ∈ X, G.Touch c d := by
  simp only [haloL, mem_sortCells, List.mem_filter, List.mem_flatMap, decide_eq_true_eq,
    hG.touch_iff]
  constructor
  · rintro ⟨⟨d, hd, hcd⟩, hc⟩; exact ⟨hc, d, hd, hcd⟩
  · rintro ⟨hc, d, hd, hcd⟩; exact ⟨⟨d, hd, hcd⟩, hc⟩

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

/-! ## Properties of a corona -/

variable {S : List Cell} {K : ℕ} {tiles : Tiles}

theorem cover_mono {j j' : ℕ} (h : j ≤ j') : cover tiles j ⊆ cover tiles j' := by
  rintro c ⟨t, ht, hl, hc⟩; exact ⟨t, ht, le_trans hl h, hc⟩

theorem mem_cover_of {t : ℕ × Finset Cell} {j : ℕ} {c : Cell} (ht : t ∈ tiles) (hl : t.1 ≤ j)
    (hc : c ∈ t.2) : c ∈ cover tiles j := ⟨t, ht, hl, hc⟩

theorem cover_zero (hc : IsCorona G S.toFinset K tiles) {c : Cell} :
    c ∈ cover tiles 0 ↔ c ∈ S := by
  constructor
  · rintro ⟨t, ht, hl, hct⟩
    have := hc.2.1.2 t ht (by omega)
    rw [this] at hct; simpa using hct
  · intro h; exact ⟨(0, S.toFinset), hc.2.1.1, le_refl _, by simpa using h⟩

theorem tile_eq_of_mem (hc : IsCorona G S.toFinset K tiles) {t u : ℕ × Finset Cell} {c : Cell}
    (ht : t ∈ tiles) (hu : u ∈ tiles) (hct : c ∈ t.2) (hcu : c ∈ u.2) : t = u := by
  by_contra hne
  exact Finset.disjoint_left.mp (hc.2.2.1 t ht u hu hne) hct hcu

theorem not_mem_cover_of_tile (hc : IsCorona G S.toFinset K tiles) {t : ℕ × Finset Cell}
    {c : Cell} {j : ℕ} (ht : t ∈ tiles) (hct : c ∈ t.2) (hj : j < t.1) :
    c ∉ cover tiles j := by
  rintro ⟨u, hu, hl, hcu⟩
  have := tile_eq_of_mem hc ht hu hct hcu
  subst this; omega

theorem tile_not_mem_S (hc : IsCorona G S.toFinset K tiles) {t : ℕ × Finset Cell} {c : Cell}
    (ht : t ∈ tiles) (h1 : 1 ≤ t.1) (hct : c ∈ t.2) : c ∉ S := by
  intro hS
  exact not_mem_cover_of_tile hc ht hct (by omega) ((cover_zero hc).mpr hS)

theorem cover_cases (hc : IsCorona G S.toFinset K tiles) {c : Cell} {j : ℕ}
    (h : c ∈ cover tiles j) (hS : c ∉ S) : ∃ u ∈ tiles, 1 ≤ u.1 ∧ u.1 ≤ j ∧ c ∈ u.2 := by
  obtain ⟨u, hu, hl, hcu⟩ := h
  refine ⟨u, hu, ?_, hl, hcu⟩
  by_contra h0
  exact hS ((cover_zero hc).mp ⟨u, hu, by omega, hcu⟩)

/-- **Lemma A**: a cell at distance `n ≤ K` from `S` lies in `P_n`. -/
theorem lemmaA (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) :
    ∀ n c, G.dist (sortCells S) c = some n → n ≤ K → c ∈ cover tiles n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hd hK
    cases n with
    | zero =>
      have := hG.dist_zero _ c hd
      exact (cover_zero hc).mpr (by simpa using this)
    | succ n =>
      obtain ⟨c', htc, m, hm, hd'⟩ := hG.dist_step _ c n hd
      have hc'P : c' ∈ cover tiles n := cover_mono hm (ih m (by omega) c' hd' (by omega))
      by_cases hcP : c ∈ cover tiles n
      · exact cover_mono (by omega) hcP
      · exact hc.2.2.2.1 n (by omega) ⟨hcP, c', hc'P, htc⟩

/-- A tile of layer `l ≥ 1` lies at distance `≥ l` from `S`. -/
theorem tile_far (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) {u : ℕ × Finset Cell}
    (hu : u ∈ tiles) (h1 : 1 ≤ u.1) {c : Cell} (hcu : c ∈ u.2) {n : ℕ}
    (hd : G.dist (sortCells S) c = some n) : u.1 ≤ n := by
  by_contra hlt
  have hK := (hc.1 u hu).1
  exact not_mem_cover_of_tile hc hu hcu (by omega) (lemmaA hG hc n c hd (by omega))

/-- (P2) for one tile: its halo lies in the next prefix. -/
theorem tile_halo_sub (hc : IsCorona G S.toFinset K tiles) {u : ℕ × Finset Cell} (hu : u ∈ tiles)
    (hK : u.1 < K) {c : Cell} (hcu : c ∉ u.2) {d : Cell} (hd : d ∈ u.2) (htd : G.Touch c d) :
    c ∈ cover tiles (u.1 + 1) := by
  by_cases hcP : c ∈ cover tiles u.1
  · exact cover_mono (by omega) hcP
  · exact hc.2.2.2.1 u.1 hK ⟨hcP, d, ⟨u, hu, le_refl _, hd⟩, htd⟩

/-- (P3) for one tile: some cell of `P_{l-1}` outside the tile touches it. -/
theorem tile_touch (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) {u : ℕ × Finset Cell}
    (hu : u ∈ tiles) (h1 : 1 ≤ u.1) :
    ∃ d ∈ cover tiles (u.1 - 1), d ∉ u.2 ∧ ∃ c ∈ u.2, G.Touch d c := by
  obtain ⟨c, hcu, hcP, d, hdP, htd⟩ := hc.2.2.2.2 u hu h1
  refine ⟨d, hdP, ?_, c, hcu, hG.touch_symm _ _ htd⟩
  intro hdu
  exact not_mem_cover_of_tile hc hu hdu (by omega) hdP

/-! ## Holes -/

theorem edgeGraph_adj (hG : GridOK G) {u v : Cell} : (edgeGraph G).Adj u v → G.EdgeAdj u v := by
  intro h
  simp only [edgeGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact h
  · exact hG.edge_symm _ _ h

/-- A nonempty list of cells outside `P` whose outer edge neighbours all lie in `P` gives a
hole of `P`. -/
theorem hasHole_of_trapped (hG : GridOK G) (P : Set Cell) (H : List Cell) (hne : H ≠ [])
    (hcell : ∀ c ∈ H, G.isCell c) (hout : ∀ c ∈ H, c ∉ P)
    (hbd : ∀ c ∈ H, ∀ d, G.EdgeAdj c d → d ∉ H → d ∈ P) :
    HasHole G P := by
  obtain ⟨c₀, hc₀⟩ := List.exists_mem_of_ne_nil H hne
  have hc : c₀ ∈ Pᶜ := hout c₀ hc₀
  refine ⟨c₀, hcell c₀ hc₀, hc, ?_⟩
  have key : ∀ (u v : ↥(Pᶜ)), ((edgeGraph G).induce Pᶜ).Walk u v → u.1 ∈ H → v.1 ∈ H := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons a b _ hadj _ ih =>
      intro ha
      apply ih
      have hab : G.EdgeAdj a.1 b.1 := edgeGraph_adj hG (SimpleGraph.comap_adj.mp hadj)
      by_contra hb
      exact b.2 (hbd a.1 ha b.1 hab hb)
  have hfin : (Subtype.val ⁻¹' {x : Cell | x ∈ H} : Set ↥(Pᶜ)).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn H.finite_toSet
  refine hfin.subset ?_
  rintro d ⟨w⟩
  exact key _ _ w hc₀

end HeeschProof
