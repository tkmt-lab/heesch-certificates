import Heesch.Main

/-!
# Heesch CNF soundness on three grids: the grid facts `GridOK` for the square, hexagon and triangle grids

* square: Chebyshev distance, as in `Heesch.Square.Basic`.
* hexagon: the hexagon norm `max(|a|, |b|, |a+b|)` decreases by one along some neighbour offset.
* triangle: `Touch` via the six triangles around a vertex point (`ring_iff`); the distance
  `triDist1 c t = 1 + min dist(u, u')` over vertices steps down along an edge of the vertex
  lattice: the triangle on that edge touches `c` and is one closer to `t` (`tri_dist_step`);
  the congruences `x ↦ m x + w` with `triTransOk` map non-cells to non-cells (`tri_copy_cell`).
-/

namespace HeeschProof

open Heesch

/-! ## Minimum of a mapped list -/

theorem min_map_some {α : Type} {l : List α} {f : α → ℕ} {d : ℕ}
    (h : (l.map f).min? = some d) : (∃ t ∈ l, f t = d) ∧ ∀ t ∈ l, d ≤ f t := by
  rw [List.min?_eq_some_iff] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h1
  exact ⟨⟨t, ht, rfl⟩, fun t' ht' => h2 _ (List.mem_map_of_mem ht')⟩

theorem min_map_le {α : Type} {l : List α} (f : α → ℕ) {t : α} (ht : t ∈ l) :
    ∃ d, (l.map f).min? = some d ∧ d ≤ f t := by
  have hne : (l.map f).min? ≠ none := by
    intro h; rw [List.min?_eq_none_iff] at h
    have := List.mem_map_of_mem (f := f) ht; rw [h] at this; simp at this
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hne
  exact ⟨d, hd, (min_map_some hd).2 t ht⟩

theorem min_le_of_mem {l : List ℕ} {x d : ℕ} (hx : x ∈ l) (h : l.min? = some d) : d ≤ x := by
  rw [List.min?_eq_some_iff] at h; exact h.2 x hx

theorem min_some_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) : ∃ d, l.min? = some d := by
  have hne : l.min? ≠ none := by
    intro h; rw [List.min?_eq_none_iff] at h; simp [h] at hx
  exact Option.ne_none_iff_exists'.mp hne

/-! ## The square grid -/

theorem cheb_le_iff {c t : Cell} {j : ℕ} :
    cheb c t ≤ j ↔ (c.1 - t.1).natAbs ≤ j ∧ (c.2 - t.2).natAbs ≤ j := by
  simp [cheb]

/-- One step towards `t`. -/
theorem cheb_step {c t : Cell} {j : ℕ} (h : cheb c t ≤ j + 1) :
    ∃ c', (c' = c ∨ squareTouch c c') ∧ cheb c' t ≤ j := by
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
      simp only [squareTouch, ne_eq, Prod.mk.injEq, abs_le]; omega
  · rw [cheb_le_iff]; simp only; constructor <;> omega

theorem squareOK : GridOK squareGrid where
  touch_iff c d := by
    change squareTouch c d ↔ c ∈ nbr8.map (shift d)
    obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
    simp only [squareTouch, nbr8, shift, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false, ne_eq, Prod.mk.injEq, abs_le, Prod.exists]
    constructor
    · rintro ⟨hne, ⟨h1, h2⟩, h3, h4⟩
      refine ⟨c1 - d1, c2 - d2, ?_, by omega, by omega⟩
      omega
    · rintro ⟨a, b, hδ, rfl, rfl⟩
      omega
  touch_symm c d := by
    change squareTouch c d → squareTouch d c
    obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
    simp only [squareTouch, ne_eq, Prod.mk.injEq, abs_le]; omega
  touch_cell _ _ _ := trivial
  edge_symm c d := by
    change squareEdgeAdj c d → squareEdgeAdj d c
    simp only [squareEdgeAdj, Int.abs_eq_natAbs]; omega
  dist_zero T0 c h := by
    obtain ⟨⟨t, ht, h0⟩, _⟩ := min_map_some (f := cheb c) h
    have : c = t := by
      obtain ⟨c1, c2⟩ := c; obtain ⟨t1, t2⟩ := t
      simp only [cheb] at h0; ext <;> simp only <;> omega
    subst this; exact ht
  dist_step T0 c n h := by
    obtain ⟨⟨t, ht, hct⟩, _⟩ := min_map_some (f := cheb c) h
    obtain ⟨c', hc', h'⟩ := cheb_step (le_of_eq hct)
    rcases hc' with rfl | htc
    · omega
    · obtain ⟨m, hm, hmle⟩ := min_map_le (cheb c') ht
      exact ⟨c', htc, m, le_trans hmle h', hm⟩
  dist_mem T0 c d hc h := by
    have := (min_map_some (f := cheb c) h).2 c hc
    simp [cheb] at this; omega
  dist_some T0 c _ h := by
    obtain ⟨t, ht, _⟩ := h
    obtain ⟨d, hd, _⟩ := min_map_le (cheb c) ht
    change (T0.map (cheb c)).min? ≠ none
    rw [hd]; simp
  copy_cell _ _ _ _ _ _ := trivial

/-! ## The hexagon grid -/

theorem mem_hexOffsets {δ : Cell} : δ ∈ hexOffsets ↔
    (δ.1 = 1 ∧ δ.2 = 0) ∨ (δ.1 = -1 ∧ δ.2 = 0) ∨ (δ.1 = 0 ∧ δ.2 = 1) ∨ (δ.1 = 0 ∧ δ.2 = -1) ∨
      (δ.1 = 1 ∧ δ.2 = -1) ∨ (δ.1 = -1 ∧ δ.2 = 1) := by
  obtain ⟨a, b⟩ := δ
  simp [hexOffsets, Prod.mk.injEq]

/-- The hexagon norm goes down by one along some neighbour offset. -/
theorem hex_step {a b : ℤ} {n : ℕ} (h : hexNorm (a, b) = n + 1) :
    ∃ δ ∈ hexOffsets, hexNorm (a + δ.1, b + δ.2) ≤ n := by
  simp only [hexNorm] at h
  by_cases h1 : 0 < a ∧ 0 ≤ b
  · exact ⟨(-1, 0), by simp [hexOffsets], by simp only [hexNorm]; omega⟩
  by_cases h2 : 0 ≤ a ∧ 0 < b
  · exact ⟨(0, -1), by simp [hexOffsets], by simp only [hexNorm]; omega⟩
  by_cases h3 : a < 0 ∧ b ≤ 0
  · exact ⟨(1, 0), by simp [hexOffsets], by simp only [hexNorm]; omega⟩
  by_cases h4 : a ≤ 0 ∧ b < 0
  · exact ⟨(0, 1), by simp [hexOffsets], by simp only [hexNorm]; omega⟩
  by_cases h5 : 0 < a ∧ b < 0
  · exact ⟨(-1, 1), by simp [hexOffsets], by simp only [hexNorm]; omega⟩
  by_cases h6 : a < 0 ∧ 0 < b
  · exact ⟨(1, -1), by simp [hexOffsets], by simp only [hexNorm]; omega⟩
  exfalso; omega

theorem hexNorm_zero {a b : ℤ} (h : hexNorm (a, b) = 0) : a = 0 ∧ b = 0 := by
  simp only [hexNorm] at h; omega

theorem hexOK : GridOK hexGrid where
  touch_iff c d := by
    change hexTouch c d ↔ c ∈ hexOffsets.map (shift d)
    obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
    simp only [hexTouch, mem_hexOffsets, List.mem_map, shift, Prod.exists, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨c1 - d1, c2 - d2, ?_, by omega, by omega⟩
      omega
    · rintro ⟨a, b, hδ, rfl, rfl⟩
      omega
  touch_symm c d := by
    change hexTouch c d → hexTouch d c
    simp only [hexTouch, mem_hexOffsets]; omega
  touch_cell _ _ _ := trivial
  edge_symm c d := by
    change hexTouch c d → hexTouch d c
    simp only [hexTouch, mem_hexOffsets]; omega
  dist_zero T0 c h := by
    obtain ⟨⟨t, ht, h0⟩, _⟩ := min_map_some h
    have := hexNorm_zero h0
    have : c = t := by ext <;> omega
    subst this; exact ht
  dist_step T0 c n h := by
    obtain ⟨⟨t, ht, hct⟩, _⟩ := min_map_some h
    obtain ⟨δ, hδ, hle⟩ := hex_step hct
    refine ⟨(c.1 + δ.1, c.2 + δ.2), ?_, ?_⟩
    · change hexTouch c _
      simp only [hexTouch]
      have : (c.1 + δ.1 - c.1, c.2 + δ.2 - c.2) = δ := by ext <;> simp
      rw [this]; exact hδ
    · obtain ⟨m, hm, hmle⟩ := min_map_le
        (fun t => hexNorm ((c.1 + δ.1, c.2 + δ.2).1 - t.1, (c.1 + δ.1, c.2 + δ.2).2 - t.2)) ht
      refine ⟨m, le_trans hmle ?_, hm⟩
      have : ((c.1 + δ.1, c.2 + δ.2).1 - t.1, (c.1 + δ.1, c.2 + δ.2).2 - t.2) =
          (c.1 - t.1 + δ.1, c.2 - t.2 + δ.2) := by ext <;> simp only <;> omega
      simp only at this ⊢
      rw [this]; exact hle
  dist_mem T0 c d hc h := by
    have := (min_map_some h).2 c hc
    simp [hexNorm] at this; omega
  dist_some T0 c _ h := by
    obtain ⟨t, ht, _⟩ := h
    obtain ⟨d, hd, _⟩ := min_map_le (fun t => hexNorm (c.1 - t.1, c.2 - t.2)) ht
    change (T0.map fun t => hexNorm (c.1 - t.1, c.2 - t.2)).min? ≠ none
    rw [hd]; simp
  copy_cell _ _ _ _ _ _ := trivial

/-! ## The triangle grid -/

theorem tv_black {c : Cell} (h1 : c.1 % 3 = 0) (h2 : c.2 % 3 = 0) :
    triVerts c = [(c.1 - 1, c.2 + 2), (c.1 - 1, c.2 - 1), (c.1 + 2, c.2 - 1)] := by
  unfold triVerts; rw [if_pos ⟨h1, h2⟩]

theorem tv_grey {c : Cell} (h1 : c.1 % 3 = 1) (h2 : c.2 % 3 = 1) :
    triVerts c = [(c.1 + 1, c.2 - 2), (c.1 + 1, c.2 + 1), (c.1 - 2, c.2 + 1)] := by
  unfold triVerts; rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

theorem tv_none {c : Cell} (h : ¬ triIsCell c) : triVerts c = [] := by
  unfold triIsCell at h
  unfold triVerts; rw [if_neg (by tauto), if_neg (by tauto)]

theorem mem_pair3 {u a b c : Cell} : u ∈ [a, b, c] ↔ u = a ∨ u = b ∨ u = c := by simp

/-- The vertices of a triangle are vertex points. -/
theorem tv_vertex {c u : Cell} (hu : u ∈ triVerts c) : u.1 % 3 = 2 ∧ u.2 % 3 = 2 := by
  by_cases hb : c.1 % 3 = 0 ∧ c.2 % 3 = 0
  · rw [tv_black hb.1 hb.2, mem_pair3] at hu
    rcases hu with rfl | rfl | rfl <;> simp only <;> omega
  by_cases hg : c.1 % 3 = 1 ∧ c.2 % 3 = 1
  · rw [tv_grey hg.1 hg.2, mem_pair3] at hu
    rcases hu with rfl | rfl | rfl <;> simp only <;> omega
  rw [tv_none (by unfold triIsCell; tauto)] at hu; simp at hu

theorem tv_cell {c u : Cell} (hu : u ∈ triVerts c) : triIsCell c := by
  by_contra h; rw [tv_none h] at hu; simp at hu

theorem tv_ne_nil {c : Cell} (h : triIsCell c) : triVerts c ≠ [] := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [tv_black h1 h2]; simp
  · rw [tv_grey h1 h2]; simp

/-- Around a vertex point `z`: `c` is one of the six triangles at `z` iff `z` is a vertex of `c`. -/
theorem ring_iff {z c : Cell} (hz : z.1 % 3 = 2 ∧ z.2 % 3 = 2) :
    c ∈ triRing z ↔ z ∈ triVerts c := by
  obtain ⟨z1, z2⟩ := z; obtain ⟨c1, c2⟩ := c
  simp only at hz
  constructor
  · intro h
    simp only [triRing, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [tv_black (by simp only; omega) (by simp only; omega), mem_pair3]; simp only [Prod.mk.injEq]; omega
    · rw [tv_grey (by simp only; omega) (by simp only; omega), mem_pair3]; simp only [Prod.mk.injEq]; omega
    · rw [tv_black (by simp only; omega) (by simp only; omega), mem_pair3]; simp only [Prod.mk.injEq]; omega
    · rw [tv_grey (by simp only; omega) (by simp only; omega), mem_pair3]; simp only [Prod.mk.injEq]; omega
    · rw [tv_black (by simp only; omega) (by simp only; omega), mem_pair3]; simp only [Prod.mk.injEq]; omega
    · rw [tv_grey (by simp only; omega) (by simp only; omega), mem_pair3]; simp only [Prod.mk.injEq]; omega
  · intro h
    simp only [triRing, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    by_cases hb : c1 % 3 = 0 ∧ c2 % 3 = 0
    · rw [tv_black hb.1 hb.2, mem_pair3] at h; simp only [Prod.mk.injEq] at h; omega
    by_cases hg : c1 % 3 = 1 ∧ c2 % 3 = 1
    · rw [tv_grey hg.1 hg.2, mem_pair3] at h; simp only [Prod.mk.injEq] at h; omega
    rw [tv_none (by unfold triIsCell; simp only; tauto)] at h; simp at h

/-- On every edge of the vertex lattice (from `u` to `u + 3δ`) lies a triangle. -/
theorem edge_tri {u δ : Cell} (hu : u.1 % 3 = 2 ∧ u.2 % 3 = 2) (hδ : δ ∈ hexOffsets) :
    ∃ c', u ∈ triVerts c' ∧ (u.1 + 3 * δ.1, u.2 + 3 * δ.2) ∈ triVerts c' := by
  obtain ⟨u1, u2⟩ := u; obtain ⟨d1, d2⟩ := δ
  simp only at hu
  rw [mem_hexOffsets] at hδ
  simp only at hδ
  rcases hδ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨(u1 + 1, u2 + 1), ?_⟩
    rw [tv_black (by simp only; omega) (by simp only; omega), mem_pair3, mem_pair3]
    simp only [Prod.mk.injEq]; omega
  · refine ⟨(u1 - 1, u2 - 1), ?_⟩
    rw [tv_grey (by simp only; omega) (by simp only; omega), mem_pair3, mem_pair3]
    simp only [Prod.mk.injEq]; omega
  · refine ⟨(u1 - 1, u2 + 2), ?_⟩
    rw [tv_grey (by simp only; omega) (by simp only; omega), mem_pair3, mem_pair3]
    simp only [Prod.mk.injEq]; omega
  · refine ⟨(u1 + 1, u2 - 2), ?_⟩
    rw [tv_black (by simp only; omega) (by simp only; omega), mem_pair3, mem_pair3]
    simp only [Prod.mk.injEq]; omega
  · refine ⟨(u1 + 2, u2 - 1), ?_⟩
    rw [tv_grey (by simp only; omega) (by simp only; omega), mem_pair3, mem_pair3]
    simp only [Prod.mk.injEq]; omega
  · refine ⟨(u1 - 2, u2 + 1), ?_⟩
    rw [tv_black (by simp only; omega) (by simp only; omega), mem_pair3, mem_pair3]
    simp only [Prod.mk.injEq]; omega

/-- The vertex-lattice distances between the vertices of `c` and of `t`. -/
def vpairs (c t : Cell) : List ℕ :=
  (triVerts c).flatMap fun u => (triVerts t).map fun u' =>
    hexNorm ((u.1 - u'.1) / 3, (u.2 - u'.2) / 3)

theorem triDist1_eq (c t : Cell) :
    triDist1 c t = if c = t then 0 else 1 + ((vpairs c t).min?.getD 0) := rfl

theorem mem_vpairs {c t u u' : Cell} (hu : u ∈ triVerts c) (hu' : u' ∈ triVerts t) :
    hexNorm ((u.1 - u'.1) / 3, (u.2 - u'.2) / 3) ∈ vpairs c t :=
  List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨u', hu', rfl⟩⟩

theorem triDist1_self (c : Cell) : triDist1 c c = 0 := by simp [triDist1_eq]

theorem triDist1_le {c t u u' : Cell} (hu : u ∈ triVerts c) (hu' : u' ∈ triVerts t) :
    triDist1 c t ≤ 1 + hexNorm ((u.1 - u'.1) / 3, (u.2 - u'.2) / 3) := by
  rw [triDist1_eq]
  split_ifs
  · omega
  · have hm := mem_vpairs hu hu'
    obtain ⟨d, hd⟩ := min_some_of_mem hm
    rw [hd, Option.getD_some]
    have := min_le_of_mem hm hd
    omega

theorem triCellB_iff {c : Cell} : triCellB c = true ↔ triIsCell c := by
  simp [triCellB, triIsCell]

/-- The triangle grid's distance, unfolded. -/
theorem tri_dist_eq (T0 : List Cell) (c : Cell) :
    triGrid.dist T0 c =
      if triCellB c then ((T0.filter triCellB).map (triDist1 c)).min? else none := rfl

theorem tri_dist_some {T0 : List Cell} {c : Cell} {d : ℕ} (h : triGrid.dist T0 c = some d) :
    triIsCell c ∧ (∃ t ∈ T0, triIsCell t ∧ triDist1 c t = d) ∧
      ∀ t ∈ T0, triIsCell t → d ≤ triDist1 c t := by
  rw [tri_dist_eq] at h
  split_ifs at h with hc
  obtain ⟨⟨t, ht, htd⟩, hmin⟩ := min_map_some h
  rw [List.mem_filter] at ht
  refine ⟨triCellB_iff.mp hc, ⟨t, ht.1, triCellB_iff.mp ht.2, htd⟩, ?_⟩
  intro t' ht' hc'
  exact hmin t' (List.mem_filter.mpr ⟨ht', triCellB_iff.mpr hc'⟩)

theorem tri_dist_le {T0 : List Cell} {c t : Cell} (hc : triIsCell c) (ht : t ∈ T0)
    (htc : triIsCell t) : ∃ m, triGrid.dist T0 c = some m ∧ m ≤ triDist1 c t := by
  rw [tri_dist_eq, if_pos (triCellB_iff.mpr hc)]
  exact min_map_le (triDist1 c) (List.mem_filter.mpr ⟨ht, triCellB_iff.mpr htc⟩)

/-- One step of the triangle distance. -/
theorem tri_dist_step {T0 : List Cell} {c : Cell} {n : ℕ}
    (h : triGrid.dist T0 c = some (n + 1)) :
    ∃ c', triTouch c c' ∧ ∃ m, m ≤ n ∧ triGrid.dist T0 c' = some m := by
  obtain ⟨hc, ⟨t, ht, htc, hct⟩, _⟩ := tri_dist_some h
  have hne : c ≠ t := by intro he; rw [he, triDist1_self] at hct; omega
  rw [triDist1_eq, if_neg hne] at hct
  -- the minimum over vertex pairs is `n`
  obtain ⟨u0, hu0⟩ := List.exists_mem_of_ne_nil _ (tv_ne_nil hc)
  obtain ⟨v0, hv0⟩ := List.exists_mem_of_ne_nil _ (tv_ne_nil htc)
  obtain ⟨d, hd⟩ := min_some_of_mem (mem_vpairs hu0 hv0)
  rw [hd, Option.getD_some] at hct
  have hdn : d = n := by omega
  subst hdn
  have hmin : ∀ u ∈ triVerts c, ∀ u' ∈ triVerts t,
      d ≤ hexNorm ((u.1 - u'.1) / 3, (u.2 - u'.2) / 3) :=
    fun u hu u' hu' => min_le_of_mem (mem_vpairs hu hu') hd
  obtain ⟨hdmem, _⟩ := List.min?_eq_some_iff.mp hd
  obtain ⟨u, hu, hdmem⟩ := List.mem_flatMap.mp hdmem
  obtain ⟨u', hu', hval⟩ := List.mem_map.mp hdmem
  have hvu := tv_vertex hu
  have hvu' := tv_vertex hu'
  cases d with
  | zero =>
    -- `c` and `t` share the vertex `u = u'`
    have := hexNorm_zero hval
    have huu : u = u' := by ext <;> omega
    subst huu
    refine ⟨t, ⟨hne, u, hu, hu'⟩, ?_⟩
    obtain ⟨m, hm, hmle⟩ := tri_dist_le htc ht htc
    rw [triDist1_self] at hmle
    exact ⟨m, hmle, hm⟩
  | succ k =>
    obtain ⟨δ, hδ, hle⟩ := hex_step hval
    obtain ⟨c', hc'u, hc'u1⟩ := edge_tri hvu hδ
    have hval1 : ((u.1 + 3 * δ.1 - u'.1) / 3, (u.2 + 3 * δ.2 - u'.2) / 3) =
        ((u.1 - u'.1) / 3 + δ.1, (u.2 - u'.2) / 3 + δ.2) := by ext <;> simp only <;> omega
    have hcc' : c ≠ c' := by
      intro he; subst he
      have := hmin _ hc'u1 u' hu'
      simp only at this; rw [hval1] at this; omega
    refine ⟨c', ⟨hcc', u, hu, hc'u⟩, ?_⟩
    obtain ⟨m, hm, hmle⟩ := tri_dist_le (tv_cell hc'u) ht htc
    refine ⟨m, ?_, hm⟩
    have h1 := triDist1_le hc'u1 hu'
    simp only at h1; rw [hval1] at h1
    by_cases hct' : c' = t
    · subst hct'; rw [triDist1_self] at hmle; omega
    · omega

theorem hexOrients_eq : hexOrients =
    [(1, 0, 0, 1), (1, 1, 0, -1), (0, -1, 1, 1), (0, 1, 1, 0), (-1, -1, 1, 0), (-1, 0, 1, 1),
     (-1, 0, 0, -1), (-1, -1, 0, 1), (0, 1, -1, -1), (0, -1, -1, 0), (1, 1, -1, 0),
     (1, 0, -1, -1)] := by decide

/-- An allowed congruence maps non-cells to non-cells. -/
theorem tri_copy_cell {m : Orient} (hm : m ∈ hexOrients) {w : Cell}
    (hw : triTransOk m w = true) {x : Cell} (h : triIsCell (place m w x)) : triIsCell x := by
  obtain ⟨w1, w2⟩ := w; obtain ⟨x1, x2⟩ := x
  rw [hexOrients_eq] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  unfold triTransOk at hw
  have hw' := of_decide_eq_true hw
  clear hw
  unfold triIsCell place applyM at h
  unfold triIsCell
  simp only [applyM] at hw'
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only at hw' h ⊢ <;> omega

theorem triOK : GridOK triGrid where
  touch_iff c d := by
    change triTouch c d ↔ c ∈ triNbrs d
    simp only [triTouch, triNbrs, List.mem_filter, List.mem_flatMap, decide_eq_true_eq]
    constructor
    · rintro ⟨hne, v, hvc, hvd⟩
      exact ⟨⟨v, hvd, (ring_iff (tv_vertex hvd)).mpr hvc⟩, hne⟩
    · rintro ⟨⟨z, hzd, hcz⟩, hne⟩
      exact ⟨hne, z, (ring_iff (tv_vertex hzd)).mp hcz, hzd⟩
  touch_symm c d := by
    change triTouch c d → triTouch d c
    rintro ⟨hne, v, hvc, hvd⟩; exact ⟨Ne.symm hne, v, hvd, hvc⟩
  touch_cell c d := by
    change triTouch c d → triIsCell c
    rintro ⟨_, v, hvc, _⟩; exact tv_cell hvc
  edge_symm c d := by
    change triEdgeAdj c d → triEdgeAdj d c
    rintro ⟨hne, v, hvc, w, hwc, hvw, hvd, hwd⟩
    exact ⟨Ne.symm hne, v, hvd, w, hwd, hvw, hvc, hwc⟩
  dist_zero T0 c h := by
    obtain ⟨_, ⟨t, ht, _, hct⟩, _⟩ := tri_dist_some h
    by_cases he : c = t
    · subst he; exact ht
    · rw [triDist1_eq, if_neg he] at hct; omega
  dist_step T0 c n h := tri_dist_step h
  dist_mem T0 c d hc h := by
    obtain ⟨hcell, _, hmin⟩ := tri_dist_some h
    have := hmin c hc hcell
    rw [triDist1_self] at this; omega
  dist_some T0 c hc h := by
    obtain ⟨t, ht, htc⟩ := h
    obtain ⟨m, hm, _⟩ := tri_dist_le hc ht htc
    rw [hm]; simp
  copy_cell m hm w hw x h := tri_copy_cell hm hw h

end HeeschProof
