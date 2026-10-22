import Heesch.Basic

/-!
# Heesch CNF soundness on three grids: every real tile survives the pruning of §4.1

For a corona `tiles` of `S.toFinset` on a grid `G` with `GridOK G`, every tile `u` of layer
`≥ 1` appears among `candidates G S K` (as the sorted list of its cells) with its layer `u.1`
allowed. This is `Heesch.Square.Cand` made generic over the grid.
-/

namespace HeeschProof

open Heesch

variable {G : Grid} {S : List Cell} {K : ℕ} {tiles : Tiles}

/-! ## Membership lemmas for the pruning -/

theorem getD_range_map {α : Type} {n i : ℕ} (f : ℕ → α) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

theorem mem_touchingCopies {T0 R : List Cell} {p : List Cell} :
    p ∈ touchingCopies G T0 R ↔
      (∃ m ∈ G.orients, ∃ r ∈ R, ∃ s ∈ T0, ∃ q ∈ G.nbrs r,
        G.transOk m (q.1 - (applyM m s).1, q.2 - (applyM m s).2) = true ∧
        p = sortCells (T0.map (place m (q.1 - (applyM m s).1, q.2 - (applyM m s).2)))) ∧
      meets p T0 = false ∧ meets (haloL G p) R = true := by
  unfold touchingCopies
  simp only [List.mem_mergeSort, List.mem_filter, List.mem_dedup, List.mem_flatMap,
    List.mem_filterMap, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨m, hm, r, hr, s, hs, q, hq, hp⟩, h1, h2⟩
    split_ifs at hp with ht
    · cases hp; exact ⟨⟨m, hm, r, hr, s, hs, q, hq, ht, rfl⟩, h1, h2⟩
  · rintro ⟨⟨m, hm, r, hr, s, hs, q, hq, ht, rfl⟩, h1, h2⟩
    exact ⟨⟨m, hm, r, hr, s, hs, q, hq, by rw [if_pos ht]⟩, h1, h2⟩

theorem touchingCopies_sorted {T0 R p : List Cell} (h : p ∈ touchingCopies G T0 R) :
    IsSorted p := by
  obtain ⟨⟨m, _, r, _, s, _, q, _, _, rfl⟩, _, _⟩ := mem_touchingCopies.mp h
  exact ⟨_, rfl⟩

theorem touchingCopies_disj {T0 R p : List Cell} (h : p ∈ touchingCopies G T0 R) :
    ∀ c ∈ p, c ∉ T0 :=
  meets_false_iff.mp (mem_touchingCopies.mp h).2.1

/-- The enumeration misses no copy: a copy `m·T0 + w` disjoint from `T0` whose halo meets `R`. -/
theorem copy_mem_touchingCopies (hG : GridOK G) {T0 R : List Cell} {m : Orient}
    (hm : m ∈ G.orients) {w : Cell} (hw : G.transOk m w = true)
    (hdisj : ∀ c ∈ sortCells (T0.map (place m w)), c ∉ T0)
    {r : Cell} (hr : r ∈ R) (hrh : r ∈ haloL G (sortCells (T0.map (place m w)))) :
    sortCells (T0.map (place m w)) ∈ touchingCopies G T0 R := by
  rw [mem_touchingCopies]
  refine ⟨?_, meets_false_iff.mpr hdisj, meets_iff.mpr ⟨r, hrh, hr⟩⟩
  obtain ⟨_, d, hd, hrd⟩ := (mem_haloL hG).mp hrh
  rw [mem_sortCells, List.mem_map] at hd
  obtain ⟨s, hs, rfl⟩ := hd
  have hq := (hG.touch_iff _ _).mp (hG.touch_symm _ _ hrd)
  have hv : ((place m w s).1 - (applyM m s).1, (place m w s).2 - (applyM m s).2) = w := by
    simp only [place]; ext <;> simp
  refine ⟨m, hm, r, hr, s, hs, place m w s, hq, ?_, ?_⟩
  · rw [hv]; exact hw
  · rw [hv]

theorem mem_firstReach_succ {T0 : List Cell} {j : ℕ} {c : Cell} :
    c ∈ firstReach G T0 K (j + 1) ↔ c ∈ firstReach G T0 K j ∨
      ∃ p ∈ touchingCopies G T0 (firstReach G T0 K j), j + 1 ≤ hiOf G T0 K p ∧ c ∈ p := by
  simp only [firstReach, mem_sortCells, List.mem_append, List.mem_flatten, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro (h | ⟨p, ⟨hp, hh⟩, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, hh, hc⟩
  · rintro (h | ⟨p, hp, hh, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, ⟨hp, hh⟩, hc⟩

theorem firstReach_mono {T0 : List Cell} {j j' : ℕ} (h : j ≤ j') {c : Cell}
    (hc : c ∈ firstReach G T0 K j) : c ∈ firstReach G T0 K j' := by
  induction h with
  | refl => exact hc
  | step _ ih => exact mem_firstReach_succ.mpr (Or.inl ih)

theorem mem_reachOf {T0 : List Cell} {Λ : List (List Cell × List ℕ)} {j : ℕ} {c : Cell} :
    c ∈ reachOf T0 Λ j ↔ c ∈ T0 ∨ ∃ pl ∈ Λ, (∃ l ∈ pl.2, l ≤ j) ∧ c ∈ pl.1 := by
  simp only [reachOf, mem_sortCells, List.mem_append, List.mem_flatten, List.mem_map,
    List.mem_filter, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨_, ⟨pl, ⟨hpl, hl⟩, rfl⟩, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨pl, hpl, hl, hc⟩
  · rintro (h | ⟨pl, hpl, hl, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨pl.1, ⟨pl, ⟨hpl, hl⟩, rfl⟩, hc⟩

theorem reachOf_mono {T0 : List Cell} {Λ : List (List Cell × List ℕ)} {j j' : ℕ} (h : j ≤ j')
    {c : Cell} (hc : c ∈ reachOf T0 Λ j) : c ∈ reachOf T0 Λ j' := by
  rw [mem_reachOf] at hc ⊢
  rcases hc with hc | ⟨pl, hpl, ⟨l, hl, hlj⟩, hc⟩
  · exact Or.inl hc
  · exact Or.inr ⟨pl, hpl, ⟨l, hl, by omega⟩, hc⟩

/-! ## The real tiles as candidate lists -/

/-- What we know about the sorted cell list of a real tile. -/
structure RealCopy (G : Grid) (S : List Cell) (K : ℕ) (tiles : Tiles) (u : ℕ × Finset Cell)
    (p : List Cell) : Prop where
  mem : ∀ c, c ∈ p ↔ c ∈ u.2
  enum : ∀ R : List Cell, ∀ r ∈ R, r ∈ haloL G p → p ∈ touchingCopies G (sortCells S) R
  hi : u.1 ≤ hiOf G (sortCells S) K p
  touch : ∃ d ∈ cover tiles (u.1 - 1), d ∈ haloL G p

theorem realCopy_exists (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles)
    {u : ℕ × Finset Cell} (hu : u ∈ tiles) (h1 : 1 ≤ u.1) : ∃ p, RealCopy G S K tiles u p := by
  obtain ⟨hK, m, hm, w, hw, hv⟩ := hc.1 u hu
  set T0 := sortCells S
  have hmem : ∀ c, c ∈ sortCells (T0.map (place m w)) ↔ c ∈ u.2 := by
    intro c; rw [hv]; simp [T0]
  obtain ⟨d, hdP, hdu, c, hcu, htd⟩ := tile_touch hG hc hu h1
  refine ⟨sortCells (T0.map (place m w)), hmem, ?_, ?_, ?_⟩
  · intro R r hr hrh
    refine copy_mem_touchingCopies hG hm hw ?_ hr hrh
    intro c' hc' hc'0
    exact tile_not_mem_S hc hu h1 ((hmem c').mp hc') (by simpa [T0] using hc'0)
  · -- the distance bound
    unfold hiOf
    have hcp : c ∈ sortCells (T0.map (place m w)) := (hmem c).mpr hcu
    have hccell : G.isCell c := hG.touch_cell _ _ (hG.touch_symm _ _ htd)
    have hT0cell : ∃ t ∈ T0, G.isCell t := by
      have : c ∈ S.toFinset.image (place m w) := hv ▸ hcu
      obtain ⟨s, hs, hsc⟩ := Finset.mem_image.mp this
      refine ⟨s, by simpa [T0] using hs, hG.copy_cell m hm w hw s (hsc ▸ hccell)⟩
    have hne1 := hG.dist_some T0 c hccell hT0cell
    obtain ⟨dc, hdc⟩ := Option.ne_none_iff_exists'.mp hne1
    have hmemL : dc ∈ (sortCells (T0.map (place m w))).filterMap (G.dist T0) :=
      List.mem_filterMap.mpr ⟨c, hcp, hdc⟩
    have hne2 : ((sortCells (T0.map (place m w))).filterMap (G.dist T0)).min? ≠ none := by
      intro h; rw [List.min?_eq_none_iff] at h; simp [h] at hmemL
    obtain ⟨mn, hmn⟩ := Option.ne_none_iff_exists'.mp hne2
    rw [hmn, Option.getD_some]
    obtain ⟨hmn1, _⟩ := List.min?_eq_some_iff.mp hmn
    obtain ⟨c', hc', hdc'⟩ := List.mem_filterMap.mp hmn1
    have := tile_far hG hc hu h1 ((hmem c').mp hc') hdc'
    omega
  · refine ⟨d, hdP, (mem_haloL hG).mpr ⟨fun h => hdu ((hmem d).mp h), c, (hmem c).mpr hcu, htd⟩⟩

/-- `P_j ⊆ R_j` for the first sequential pass. -/
theorem cover_sub_firstReach (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) :
    ∀ j, ∀ c ∈ cover tiles j, c ∈ firstReach G (sortCells S) K j := by
  intro j
  induction j with
  | zero =>
    intro c h; change c ∈ sortCells S
    simpa using (cover_zero hc).mp h
  | succ j ih =>
    intro c h
    by_cases hS : c ∈ S
    · exact firstReach_mono (Nat.zero_le _) (show c ∈ sortCells S by simpa using hS)
    obtain ⟨u, hu, h1, hl, hcu⟩ := cover_cases hc h hS
    by_cases hlj : u.1 ≤ j
    · exact mem_firstReach_succ.mpr (Or.inl (ih c (mem_cover_of hu hlj hcu)))
    · have hl' : u.1 = j + 1 := by omega
      obtain ⟨p, hp⟩ := realCopy_exists hG hc hu h1
      obtain ⟨d, hdP, hdh⟩ := hp.touch
      rw [hl'] at hdP
      refine mem_firstReach_succ.mpr (Or.inr ⟨p, hp.enum _ d (ih d hdP) hdh, ?_, ?_⟩)
      · have := hp.hi; omega
      · exact (hp.mem c).mpr hcu

/-! ## The invariant of the re-filtering -/

/-- `Λ` has the right shape and keeps every real tile at its layer. -/
def Good (G : Grid) (S : List Cell) (K : ℕ) (tiles : Tiles) (Λ : List (List Cell × List ℕ)) :
    Prop :=
  (∀ pl ∈ Λ, pl.1 ∈ touchingCopies G (sortCells S) (firstReach G (sortCells S) K (K - 1)) ∧
    ∀ j ∈ pl.2, 1 ≤ j ∧ j ≤ K) ∧
  (∀ u ∈ tiles, 1 ≤ u.1 → ∃ pl ∈ Λ, (∀ c, c ∈ pl.1 ↔ c ∈ u.2) ∧ u.1 ∈ pl.2)

theorem cover_sub_reachOf (hc : IsCorona G S.toFinset K tiles) {Λ : List (List Cell × List ℕ)}
    (hΛ : Good G S K tiles Λ) {j : ℕ} {c : Cell} (h : c ∈ cover tiles j) :
    c ∈ reachOf (sortCells S) Λ j := by
  rw [mem_reachOf]
  by_cases hS : c ∈ S
  · exact Or.inl (by simpa using hS)
  obtain ⟨u, hu, h1, hl, hcu⟩ := cover_cases hc h hS
  obtain ⟨pl, hpl, hmem, hupl⟩ := hΛ.2 u hu h1
  exact Or.inr ⟨pl, hpl, ⟨u.1, hupl, hl⟩, (hmem c).mpr hcu⟩

theorem firstLayers_good (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) :
    Good G S K tiles (firstLayers G (sortCells S) K) := by
  constructor
  · intro pl hpl
    simp only [firstLayers, List.mem_map] at hpl
    obtain ⟨p, hp, rfl⟩ := hpl
    refine ⟨hp, ?_⟩
    intro j hj
    simp only [List.mem_filter, List.mem_map, List.mem_range] at hj
    omega
  · intro u hu h1
    have hK := (hc.1 u hu).1
    obtain ⟨p, hp⟩ := realCopy_exists hG hc hu h1
    obtain ⟨d, hdP, hdh⟩ := hp.touch
    have hdR := cover_sub_firstReach hG hc _ d hdP
    refine ⟨_, List.mem_map.mpr ⟨p, hp.enum _ d (firstReach_mono (by omega) hdR) hdh, rfl⟩,
      hp.mem, ?_⟩
    simp only [List.mem_filter, List.mem_map, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq]
    refine ⟨⟨u.1 - 1, by omega, by omega⟩, hp.hi, ?_⟩
    rw [getD_range_map _ _ (by omega)]
    exact meets_iff.mpr ⟨d, hdh, hdR⟩

theorem refine_good (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles)
    {Λ : List (List Cell × List ℕ)}
    (hΛ : Good G S K tiles Λ) : Good G S K tiles (refine G (sortCells S) K Λ) := by
  constructor
  · intro pl hpl
    simp only [refine, List.mem_map] at hpl
    obtain ⟨pl', hpl', rfl⟩ := hpl
    refine ⟨(hΛ.1 pl' hpl').1, ?_⟩
    intro j hj
    exact (hΛ.1 pl' hpl').2 j (List.mem_filter.mp hj).1
  · intro u hu h1
    have hK := (hc.1 u hu).1
    obtain ⟨pl, hpl, hmem, hupl⟩ := hΛ.2 u hu h1
    refine ⟨_, List.mem_map.mpr ⟨pl, hpl, rfl⟩, hmem, ?_⟩
    simp only [List.mem_filter, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      List.all_eq_true]
    refine ⟨hupl, ?_, ?_⟩
    · rw [getD_range_map _ _ (by omega)]
      obtain ⟨d, hdP, hdu, c, hcu, htd⟩ := tile_touch hG hc hu h1
      refine meets_iff.mpr ⟨d, (mem_haloL hG).mpr ⟨fun h => hdu ((hmem d).mp h), c,
        (hmem c).mpr hcu, htd⟩, cover_sub_reachOf hc hΛ hdP⟩
    · by_cases hKu : K ≤ u.1
      · exact Or.inl hKu
      · right
        intro c hc'
        rw [getD_range_map _ _ (by omega)]
        obtain ⟨hch, _⟩ := hc'
        obtain ⟨hcp, d, hd, htd⟩ := (mem_haloL hG).mp hch
        exact (cover_sub_reachOf hc hΛ
          (tile_halo_sub hc hu (by omega) (fun h => hcp ((hmem c).mpr h)) ((hmem d).mp hd) htd))

theorem fixLayers_good (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) :
    ∀ n Λ, Good G S K tiles Λ → Good G S K tiles (fixLayers G (sortCells S) K n Λ) := by
  intro n
  induction n with
  | zero => intro Λ h; exact h
  | succ n ih =>
    intro Λ h
    unfold fixLayers
    dsimp only
    split_ifs
    · exact h
    · exact ih _ (refine_good hG hc h)

/-! ## Summary: the candidates -/

theorem candidates_good (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) :
    Good G S K tiles (candidates G S K) := by
  have h := fixLayers_good hG hc
    (((firstLayers G (sortCells S) K).map fun pl => pl.2.length).sum + 1) _
    (firstLayers_good hG hc)
  unfold candidates
  dsimp only
  refine ⟨fun pl hpl => h.1 pl (List.mem_filter.mp hpl).1, ?_⟩
  intro u hu h1
  obtain ⟨pl, hpl, hmem, hupl⟩ := h.2 u hu h1
  refine ⟨pl, List.mem_filter.mpr ⟨hpl, ?_⟩, hmem, hupl⟩
  cases hpl2 : pl.2 with
  | nil => rw [hpl2] at hupl; simp at hupl
  | cons _ _ => rfl

end HeeschProof
