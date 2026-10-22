import Heesch.Square.Basic

/-!
# Heesch CNF soundness (polyominoes), properties of a corona

For a corona `tiles` of `S.toFinset` (only (P0)–(P3)): `P_0 = S`, monotonicity, the distance
lemma (Lemma A: a cell at Chebyshev distance `≤ j ≤ K` from `S` lies in `P_j`), the halo facts
used by the clauses, and the hole lemma (a nonempty finite set outside `P` whose edge boundary
lies in `P` is a hole of `P`).
-/

namespace HeeschSquareProof

open HeeschSquare

variable {S : List Cell} {K : ℕ} {tiles : Tiles}

theorem cover_mono {j j' : ℕ} (h : j ≤ j') : cover tiles j ⊆ cover tiles j' := by
  rintro c ⟨t, ht, hl, hc⟩; exact ⟨t, ht, le_trans hl h, hc⟩

theorem mem_cover_of {t : ℕ × Finset Cell} {j : ℕ} {c : Cell} (ht : t ∈ tiles) (hl : t.1 ≤ j)
    (hc : c ∈ t.2) : c ∈ cover tiles j := ⟨t, ht, hl, hc⟩

theorem cover_zero (hc : IsCorona S.toFinset K tiles) {c : Cell} :
    c ∈ cover tiles 0 ↔ c ∈ S := by
  constructor
  · rintro ⟨t, ht, hl, hct⟩
    have := hc.2.1.2 t ht (by omega)
    rw [this] at hct; simpa using hct
  · intro h; exact ⟨(0, S.toFinset), hc.2.1.1, le_refl _, by simpa using h⟩

theorem tile_eq_of_mem (hc : IsCorona S.toFinset K tiles) {t u : ℕ × Finset Cell} {c : Cell}
    (ht : t ∈ tiles) (hu : u ∈ tiles) (hct : c ∈ t.2) (hcu : c ∈ u.2) : t = u := by
  by_contra hne
  exact Finset.disjoint_left.mp (hc.2.2.1 t ht u hu hne) hct hcu

theorem not_mem_cover_of_tile (hc : IsCorona S.toFinset K tiles) {t : ℕ × Finset Cell}
    {c : Cell} {j : ℕ} (ht : t ∈ tiles) (hct : c ∈ t.2) (hj : j < t.1) :
    c ∉ cover tiles j := by
  rintro ⟨u, hu, hl, hcu⟩
  have := tile_eq_of_mem hc ht hu hct hcu
  subst this; omega

theorem tile_not_mem_S (hc : IsCorona S.toFinset K tiles) {t : ℕ × Finset Cell} {c : Cell}
    (ht : t ∈ tiles) (h1 : 1 ≤ t.1) (hct : c ∈ t.2) : c ∉ S := by
  intro hS
  exact not_mem_cover_of_tile hc ht hct (by omega) ((cover_zero hc).mpr hS)

theorem cover_cases (hc : IsCorona S.toFinset K tiles) {c : Cell} {j : ℕ}
    (h : c ∈ cover tiles j) (hS : c ∉ S) : ∃ u ∈ tiles, 1 ≤ u.1 ∧ u.1 ≤ j ∧ c ∈ u.2 := by
  obtain ⟨u, hu, hl, hcu⟩ := h
  refine ⟨u, hu, ?_, hl, hcu⟩
  by_contra h0
  exact hS ((cover_zero hc).mp ⟨u, hu, by omega, hcu⟩)

/-- **Lemma A**: a cell within Chebyshev distance `j ≤ K` of a cell of `S` lies in `P_j`. -/
theorem lemmaA (hc : IsCorona S.toFinset K tiles) {t : Cell} (ht : t ∈ S) :
    ∀ j, j ≤ K → ∀ c, cheb c t ≤ j → c ∈ cover tiles j := by
  intro j
  induction j with
  | zero =>
    intro _ c h
    have : c = t := by
      obtain ⟨c1, c2⟩ := c; obtain ⟨t1, t2⟩ := t
      rw [cheb_le_iff] at h; simp only at h; ext <;> simp only <;> omega
    subst this; exact (cover_zero hc).mpr ht
  | succ j ih =>
    intro hj c h
    obtain ⟨c', hc', h'⟩ := cheb_step h
    have hc'P := ih (by omega) c' h'
    rcases hc' with rfl | htc
    · exact cover_mono (by omega) hc'P
    · by_cases hcP : c ∈ cover tiles j
      · exact cover_mono (by omega) hcP
      · exact hc.2.2.2.1 j (by omega) ⟨hcP, c', hc'P, htc⟩

/-- A tile of layer `l ≥ 1` lies at distance `≥ l` from `S`. -/
theorem tile_far (hc : IsCorona S.toFinset K tiles) {u : ℕ × Finset Cell} (hu : u ∈ tiles)
    (h1 : 1 ≤ u.1) {c t : Cell} (hcu : c ∈ u.2) (ht : t ∈ S) : u.1 ≤ cheb c t := by
  by_contra hlt
  have hK := (hc.1 u hu).1
  exact not_mem_cover_of_tile hc hu hcu (by omega)
    (lemmaA hc ht (u.1 - 1) (by omega) c (by omega))

/-- (P2) for one tile: its halo lies in the next prefix. -/
theorem tile_halo_sub (hc : IsCorona S.toFinset K tiles) {u : ℕ × Finset Cell} (hu : u ∈ tiles)
    (hK : u.1 < K) {c : Cell} (hcu : c ∉ u.2) {d : Cell} (hd : d ∈ u.2) (htd : Touch c d) :
    c ∈ cover tiles (u.1 + 1) := by
  by_cases hcP : c ∈ cover tiles u.1
  · exact cover_mono (by omega) hcP
  · exact hc.2.2.2.1 u.1 hK ⟨hcP, d, ⟨u, hu, le_refl _, hd⟩, htd⟩

/-- (P3) for one tile: some cell of `P_{l-1}` outside the tile touches it. -/
theorem tile_touch (hc : IsCorona S.toFinset K tiles) {u : ℕ × Finset Cell} (hu : u ∈ tiles)
    (h1 : 1 ≤ u.1) : ∃ d ∈ cover tiles (u.1 - 1), d ∉ u.2 ∧ ∃ c ∈ u.2, Touch d c := by
  obtain ⟨c, hcu, hcP, d, hdP, htd⟩ := hc.2.2.2.2 u hu h1
  refine ⟨d, hdP, ?_, c, hcu, touch_symm htd⟩
  intro hdu
  exact not_mem_cover_of_tile hc hu hdu (by omega) hdP

/-! ## Holes -/

theorem edgeGraph_adj {u v : Cell} : edgeGraph.Adj u v → EdgeAdj u v := by
  intro h
  simp only [edgeGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact h
  · exact edgeAdj_symm h

/-- A nonempty list of cells outside `P` whose outer edge neighbours all lie in `P` gives a
hole of `P`. -/
theorem hasHole_of_trapped (P : Set Cell) (H : List Cell) (hne : H ≠ [])
    (hout : ∀ c ∈ H, c ∉ P) (hbd : ∀ c ∈ H, ∀ d, EdgeAdj c d → d ∉ H → d ∈ P) :
    HasHole P := by
  obtain ⟨c₀, hc₀⟩ := List.exists_mem_of_ne_nil H hne
  have hc : c₀ ∈ Pᶜ := hout c₀ hc₀
  refine ⟨c₀, hc, ?_⟩
  have key : ∀ (u v : ↥(Pᶜ)), (edgeGraph.induce Pᶜ).Walk u v → u.1 ∈ H → v.1 ∈ H := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons a b _ hadj _ ih =>
      intro ha
      apply ih
      have hab : EdgeAdj a.1 b.1 := edgeGraph_adj (SimpleGraph.comap_adj.mp hadj)
      by_contra hb
      exact b.2 (hbd a.1 ha b.1 hab hb)
  have hfin : (Subtype.val ⁻¹' {x : Cell | x ∈ H} : Set ↥(Pᶜ)).Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn H.finite_toSet
  refine hfin.subset ?_
  rintro d ⟨w⟩
  exact key _ _ w hc₀

end HeeschSquareProof
