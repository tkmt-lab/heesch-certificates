import Heesch.Ord

/-!
# Heesch CNF soundness on three grids: the clauses under the corona assignment, and the assembly

(F), (Y1), (Y2), (B), (D), (E); the "at most one" clauses (C) for every input order; the hole
clauses (H); then `sat_of_corona` and the soundness theorems for every grid with `GridOK`.
This is `Heesch.Square.Clauses`, `Heesch.Square.Amo`, `Heesch.Square.Hole` and `Heesch.Square.Main`
made generic over the grid.
-/

namespace HeeschProof

open Heesch

variable {G : Grid} {ord : Cell → List ℤ → List ℤ} {S : List Cell} {K : ℕ} {tiles : Tiles}

/-- The clause set `F` is satisfied by `σ`. -/
def AllSat (σ : ℕ → Bool) (F : CNF) : Prop := ∀ C ∈ F, ∃ l ∈ C, LitTrue σ l

/-- A cell of `hFCells`: `d(c) ∈ 1..K`, and `c ∈ P_{d(c)}`. -/
theorem fCells_props (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) {c : Cell}
    (h : c ∈ hFCells G S K) :
    ∃ d, G.dist (sortCells S) c = some d ∧ 1 ≤ d ∧ d ≤ K ∧ c ∉ S ∧ c ∈ cover tiles d := by
  unfold hFCells at h
  rw [List.mem_filter] at h
  obtain ⟨_, h⟩ := h
  cases hd : G.dist (sortCells S) c with
  | none => rw [hd] at h; simp at h
  | some d =>
    rw [hd] at h
    simp only [decide_eq_true_eq] at h
    refine ⟨d, rfl, h.1, h.2, ?_, ?_⟩
    · intro hcS
      have := hG.dist_mem _ c d (by simpa using hcS) hd
      omega
    · exact lemmaA hG hc d c hd h.2

theorem sat_F (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) :
    AllSat (hσ G ord S K tiles) (hClF G S K) := by
  intro C hC
  simp only [hClF, List.mem_map] at hC
  obtain ⟨c, hcF, rfl⟩ := hC
  unfold hFOk at hcF
  rw [List.mem_filter] at hcF
  obtain ⟨hcF, hcR⟩ := hcF
  obtain ⟨d, hd, h1, h2, hcS, hcP⟩ := fCells_props hG hc hcF
  rw [hd, Option.getD_some] at hcR ⊢
  simp only [decide_eq_true_eq] at hcR
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  have hy : (c, d) ∈ hYPairs G S K := mem_hYPairs.mpr ⟨⟨h1, h2⟩, hcR, hcS⟩
  exact (lit_hY hy).mpr hcP

theorem clBad_nil (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) : hClBad G ord S K = [] := by
  unfold hClBad
  rw [if_neg]
  unfold hFOk
  rw [List.filter_eq_self.mpr]
  · omega
  · intro c hcF
    obtain ⟨d, hd, _, h2, _, hcP⟩ := fCells_props hG hc hcF
    rw [hd, Option.getD_some]
    exact decide_eq_true (cover_sub_hR hG hc (by omega) hcP)

theorem sat_Y1 : AllSat (hσ G ord S K tiles) (hClY1 G S K) := by
  intro C hC
  simp only [hClY1, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_filter,
    decide_eq_true_eq, mem_sortCells] at hC
  obtain ⟨j, ⟨i, hi, rfl⟩, c, ⟨hcR, hcS⟩, rfl⟩ := hC
  have hy1 : (c, i + 2 - 1) ∈ hYPairs G S K := mem_hYPairs.mpr ⟨⟨by omega, by omega⟩, hcR, hcS⟩
  have hy2 : (c, i + 2) ∈ hYPairs G S K :=
    mem_hYPairs.mpr ⟨⟨by omega, by omega⟩, hR_mono (by omega) (by omega) hcR, hcS⟩
  by_cases hP : c ∈ cover tiles (i + 2 - 1)
  · exact ⟨_, by simp, (lit_hY hy2).mpr (cover_mono (by omega) hP)⟩
  · exact ⟨_, by simp, (lit_neg_hY hy1).mpr hP⟩

theorem sat_Y2 (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) : AllSat (hσ G ord S K tiles) (hClY2 G S K) := by
  intro C hC
  simp only [hClY2, hLayers, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_filter,
    decide_eq_true_eq, mem_sortCells] at hC
  obtain ⟨j, ⟨i, hi, rfl⟩, c, ⟨hcR, hcS⟩, rfl⟩ := hC
  have hy : (c, i + 1) ∈ hYPairs G S K := mem_hYPairs.mpr ⟨⟨by omega, by omega⟩, hcR, hcS⟩
  by_cases hP : c ∈ cover tiles (i + 1)
  · obtain ⟨u, hu, h1, hl, hcu⟩ := cover_cases hc hP hcS
    by_cases hlt : u.1 < i + 1
    · have hP' : c ∈ cover tiles (i + 1 - 1) := mem_cover_of hu (by omega) hcu
      have hR' := cover_sub_hR (S := S) hG hc (by omega) hP'
      have hy' : (c, i + 1 - 1) ∈ hYPairs G S K := mem_hYPairs.mpr ⟨⟨by omega, by omega⟩, hR', hcS⟩
      refine ⟨hY G S K c (i + 1 - 1), ?_, (lit_hY hy').mpr hP'⟩
      simp only [List.mem_append, List.mem_cons]
      left; right; rw [if_pos ⟨by omega, hR'⟩]; simp
    · have hl' : u.1 = i + 1 := by omega
      obtain ⟨p, hp, hmem, hreal⟩ := real_mem_tPairs (S := S) hG hc hu h1
      rw [hl'] at hp hreal
      refine ⟨hT G S K p (i + 1), ?_, (lit_hT hp).mpr hreal⟩
      simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
      right; exact ⟨(p, i + 1), ⟨hp, rfl, (hmem c).mpr hcu⟩, rfl⟩
  · exact ⟨_, by simp, (lit_neg_hY hy).mpr hP⟩

theorem real_tile {pj : List Cell × ℕ} (h : RealTile tiles pj) :
    (pj.2, pj.1.toFinset) ∈ tiles := h

theorem sat_B (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) : AllSat (hσ G ord S K tiles) (hClB G S K) := by
  intro C hC
  simp only [hClB, List.mem_flatMap, List.mem_map] at hC
  obtain ⟨pj, hpj, c, hcp, rfl⟩ := hC
  obtain ⟨_, hdisj, h1, h2, hR⟩ := tPairs_props hG hc hpj
  have hy : (c, pj.2) ∈ hYPairs G S K :=
    mem_hYPairs.mpr ⟨⟨h1, h2⟩, hR c hcp, hdisj c hcp⟩
  by_cases hr : RealTile tiles pj
  · exact ⟨_, by simp, (lit_hY hy).mpr (mem_cover_of (real_tile hr) (le_refl _)
      (by simpa using hcp))⟩
  · exact ⟨_, by simp, (lit_neg_hT hpj).mpr hr⟩

theorem sat_D (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) : AllSat (hσ G ord S K tiles) (hClD G S K) := by
  intro C hC
  simp only [hClD, List.mem_flatMap] at hC
  obtain ⟨pj, hpj, hC⟩ := hC
  split_ifs at hC with hK
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, mem_sortCells] at hC
    obtain ⟨c, ⟨hch, hcS⟩, rfl⟩ := hC
    by_cases hr : RealTile tiles pj
    · obtain ⟨hcp, d, hd, htd⟩ := (mem_haloL hG).mp hch
      have hP : c ∈ cover tiles (pj.2 + 1) :=
        tile_halo_sub hc (real_tile hr) hK (by simpa using hcp) (by simpa using hd) htd
      have hR' := cover_sub_hR (S := S) hG hc (by omega) hP
      have h1 := (tPairs_props hG hc hpj).2.2.1
      have hy : (c, pj.2 + 1) ∈ hYPairs G S K :=
        mem_hYPairs.mpr ⟨⟨by omega, by omega⟩, hR', hcS⟩
      refine ⟨hY G S K c (pj.2 + 1), ?_, (lit_hY hy).mpr hP⟩
      rw [if_pos hR']; simp
    · exact ⟨_, by simp, (lit_neg_hT hpj).mpr hr⟩
  · simp at hC

theorem sat_E (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) : AllSat (hσ G ord S K tiles) (hClE G S K) := by
  intro C hC
  simp only [hClE, List.mem_flatMap] at hC
  obtain ⟨pj, hpj, hC⟩ := hC
  split_ifs at hC with hE
  · rw [List.mem_singleton] at hC
    subst hC
    by_cases hr : RealTile tiles pj
    · obtain ⟨d, hdP, hdu, c, hcu, htd⟩ := tile_touch hG hc (real_tile hr) (by simp; omega)
      simp only at hdP hdu hcu
      have hdh : d ∈ haloL G pj.1 :=
        (mem_haloL hG).mpr ⟨by simpa using hdu, c, by simpa using hcu, htd⟩
      have hdS : d ∉ sortCells S := meets_false_iff.mp hE.2 d hdh
      have hR' := cover_sub_hR (S := S) hG hc (by have := (tPairs_props hG hc hpj).2.2.2.1; omega) hdP
      have h2 := (tPairs_props hG hc hpj).2.2.2.1
      have hy : (d, pj.2 - 1) ∈ hYPairs G S K :=
        mem_hYPairs.mpr ⟨⟨by omega, by omega⟩, hR', by simpa using hdS⟩
      refine ⟨hY G S K d (pj.2 - 1), ?_, (lit_hY hy).mpr hdP⟩
      simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
      right; exact ⟨d, ⟨hdh, hR', hdS⟩, rfl⟩
    · exact ⟨_, by simp, (lit_neg_hT hpj).mpr hr⟩
  · simp at hC



theorem getD_of_lt {α : Type} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem litTrue_zero (σ : ℕ → Bool) : ¬ LitTrue σ 0 := by simp [LitTrue]

theorem litTrue_neg_iff {σ : ℕ → Bool} {l : ℤ} (h : l ≠ 0) : LitTrue σ (-l) ↔ ¬ LitTrue σ l := by
  simp only [LitTrue, Int.natAbs_neg]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rintro (⟨h3, h4⟩ | ⟨h3, h4⟩) <;> simp_all <;> omega
  · intro hn
    rcases lt_or_gt_of_ne h with h' | h'
    · left; refine ⟨by omega, ?_⟩
      by_contra h5; exact hn (Or.inr ⟨h', by simpa using h5⟩)
    · right; refine ⟨by omega, ?_⟩
      by_contra h5; exact hn (Or.inl ⟨h', by simpa using h5⟩)

/-- **The sequential counter is sound for any input order**: if at most one input is true and
`s_a ↔ x_1 ∨ … ∨ x_a`, all clauses of `amoClauses xs base` hold. -/
theorem amo_sat (σ : ℕ → Bool) (xs : List ℤ) (base : ℕ) (hx : ∀ l ∈ xs, l ≠ 0)
    (hs : ∀ a, 1 ≤ a → a ≤ xs.length - 1 →
      (σ (base + a) = true ↔ ∃ b, 1 ≤ b ∧ b ≤ a ∧ LitTrue σ (xs.getD (b - 1) 0)))
    (hamo : ∀ b b', 1 ≤ b → b ≤ xs.length → 1 ≤ b' → b' ≤ xs.length →
      LitTrue σ (xs.getD (b - 1) 0) → LitTrue σ (xs.getD (b' - 1) 0) → b = b') :
    AllSat σ (amoClauses xs base) := by
  intro C hC
  unfold amoClauses at hC
  simp only at hC
  split_ifs at hC with hm
  · simp at hC
  have hx' : ∀ a, 1 ≤ a → a ≤ xs.length → xs.getD (a - 1) 0 ≠ 0 := by
    intro a h1 h2
    rw [getD_of_lt (by omega)]
    exact hx _ (List.getElem_mem _)
  have hsT : ∀ a, 1 ≤ a → a ≤ xs.length - 1 →
      (LitTrue σ (((base + a : ℕ) : ℤ)) ↔ ∃ b, 1 ≤ b ∧ b ≤ a ∧ LitTrue σ (xs.getD (b - 1) 0)) := by
    intro a h1 h2; rw [litTrue_pos (by omega)]; exact hs a h1 h2
  have hsF : ∀ a, 1 ≤ a → a ≤ xs.length - 1 →
      (LitTrue σ (-((base + a : ℕ) : ℤ)) ↔ ¬ ∃ b, 1 ≤ b ∧ b ≤ a ∧ LitTrue σ (xs.getD (b - 1) 0)) := by
    intro a h1 h2; rw [litTrue_neg (by omega), ← hs a h1 h2]; simp
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_map, List.mem_range] at hC
  rcases hC with (rfl | ⟨a, ⟨i, hi, rfl⟩, hC⟩) | rfl
  · -- `x_1 → s_1`
    by_cases h1 : LitTrue σ (xs.getD (1 - 1) 0)
    · exact ⟨_, by simp, (hsT 1 le_rfl (by omega)).mpr ⟨1, le_rfl, le_rfl, h1⟩⟩
    · exact ⟨_, by simp, (litTrue_neg_iff (hx' 1 le_rfl (by omega))).mpr h1⟩
  · rcases hC with rfl | rfl | rfl
    · by_cases h1 : LitTrue σ (xs.getD (i + 2 - 1) 0)
      · exact ⟨_, by simp, (hsT (i + 2) (by omega) (by omega)).mpr ⟨i + 2, by omega, le_rfl, h1⟩⟩
      · exact ⟨_, by simp, (litTrue_neg_iff (hx' (i + 2) (by omega) (by omega))).mpr h1⟩
    · by_cases h1 : ∃ b, 1 ≤ b ∧ b ≤ i + 2 - 1 ∧ LitTrue σ (xs.getD (b - 1) 0)
      · obtain ⟨b, hb1, hb2, hb⟩ := h1
        exact ⟨_, by simp, (hsT (i + 2) (by omega) (by omega)).mpr ⟨b, hb1, by omega, hb⟩⟩
      · exact ⟨_, by simp, (hsF (i + 2 - 1) (by omega) (by omega)).mpr h1⟩
    · by_cases h1 : LitTrue σ (xs.getD (i + 2 - 1) 0)
      · refine ⟨_, by simp, (hsF (i + 2 - 1) (by omega) (by omega)).mpr ?_⟩
        rintro ⟨b, hb1, hb2, hb⟩
        have := hamo b (i + 2) hb1 (by omega) (by omega) (by omega) hb h1
        omega
      · exact ⟨_, by simp, (litTrue_neg_iff (hx' (i + 2) (by omega) (by omega))).mpr h1⟩
  · -- `x_m → ¬ s_{m-1}`
    by_cases h1 : LitTrue σ (xs.getD (xs.length - 1) 0)
    · refine ⟨_, by simp, (hsF (xs.length - 1) (by omega) le_rfl).mpr ?_⟩
      rintro ⟨b, hb1, hb2, hb⟩
      have := hamo b xs.length hb1 (by omega) (by omega) le_rfl hb h1
      omega
    · exact ⟨_, by simp, (litTrue_neg_iff (hx' xs.length (by omega) le_rfl)).mpr h1⟩

/-! ## Prefix sums -/

theorem take_sum_le_succ (l : List ℕ) (k : ℕ) : (l.take k).sum ≤ (l.take (k + 1)).sum := by
  rw [List.take_succ, List.sum_append]; omega

theorem take_sum_mono (l : List ℕ) {k k' : ℕ} (h : k ≤ k') :
    (l.take k).sum ≤ (l.take k').sum := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (take_sum_le_succ l _)

theorem take_sum_succ (l : List ℕ) {k : ℕ} (h : k < l.length) :
    (l.take (k + 1)).sum = (l.take k).sum + l[k] := by
  rw [List.take_succ, List.sum_append, List.getElem?_eq_getElem h]; simp

/-- The counter slots of different groups are disjoint. -/
theorem slot_unique (l : List ℕ) {k k' a a' : ℕ} (hk : k < l.length) (hk' : k' < l.length)
    (ha : 1 ≤ a) (ha2 : a ≤ l[k]) (ha' : 1 ≤ a') (ha2' : a' ≤ l[k'])
    (h : (l.take k).sum + a = (l.take k').sum + a') : k = k' ∧ a = a' := by
  rcases lt_trichotomy k k' with hlt | rfl | hgt
  · have h1 := take_sum_succ l hk
    have h2 := take_sum_mono l (show k + 1 ≤ k' by omega)
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 := take_sum_succ l hk'
    have h2 := take_sum_mono l (show k' + 1 ≤ k by omega)
    omega

/-! ## (C) -/

variable {G : Grid} {ord : Cell → List ℤ → List ℤ} {S : List Cell} {K : ℕ} {tiles : Tiles}

theorem hσ_tidx {i : ℕ} (hi : i < hNT G S K) :
    hσ G ord S K tiles (i + 1) = true ↔ RealTile tiles ((hTPairs G S K).getD i ([], 0)) ∧
      posOf ((hTPairs G S K).getD i ([], 0)) (hTPairs G S K) = some i := by
  rw [hσ_low (by omega)]
  unfold hσ0
  rw [if_pos (by omega)]
  simp only [Nat.add_sub_cancel, decide_eq_true_eq]

theorem mem_hGroup0 {c : Cell} {x : ℤ} :
    x ∈ hGroup0 G S K c ↔ ∃ i < hNT G S K, c ∈ ((hTPairs G S K).getD i ([], 0)).1 ∧ x = ((i + 1 : ℕ) : ℤ) := by
  simp only [hGroup0, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hi, hc⟩, rfl⟩; exact ⟨i, hi, hc, rfl⟩
  · rintro ⟨i, hi, hc, rfl⟩; exact ⟨i, ⟨hi, hc⟩, rfl⟩

theorem hGroup0_nodup (c : Cell) : (hGroup0 G S K c).Nodup := by
  unfold hGroup0
  refine List.Nodup.map ?_ (List.nodup_range.filter _)
  intro a b h; simp only [Nat.cast_inj] at h; omega

/-- At most one input of a cell's counter is true. -/
theorem hGroup0_amo (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) {c : Cell} {x x' : ℤ}
    (hx : x ∈ hGroup0 G S K c) (hx' : x' ∈ hGroup0 G S K c)
    (h : LitTrue (hσ G ord S K tiles) x) (h' : LitTrue (hσ G ord S K tiles) x') : x = x' := by
  obtain ⟨i, hi, hci, rfl⟩ := mem_hGroup0.mp hx
  obtain ⟨i', hi', hci', rfl⟩ := mem_hGroup0.mp hx'
  rw [litTrue_pos (by omega), hσ_tidx hi] at h
  rw [litTrue_pos (by omega), hσ_tidx hi'] at h'
  set pj := (hTPairs G S K).getD i ([], 0)
  set pj' := (hTPairs G S K).getD i' ([], 0)
  have hmem : pj ∈ hTPairs G S K := by
    simp only [pj, getD_of_lt hi]; exact List.getElem_mem _
  have hmem' : pj' ∈ hTPairs G S K := by
    simp only [pj', getD_of_lt hi']; exact List.getElem_mem _
  have heq := tile_eq_of_mem hc (real_tile h.1) (real_tile h'.1)
    (by simpa using hci) (by simpa using hci')
  simp only [Prod.mk.injEq] at heq
  have hp : pj.1 = pj'.1 := by
    apply IsSorted.eq (tPairs_props hG hc hmem).1 (tPairs_props hG hc hmem').1
    intro d
    have := congrArg (fun s : Finset Cell => d ∈ s) heq.2
    simpa using this
  have hpp : pj = pj' := Prod.ext hp heq.1
  have := h.2
  rw [hpp, h'.2] at this
  simp only [Option.some.injEq] at this
  rw [this]

theorem length_hAux : (hAux G ord S K).length = (hGroups G ord S K).length := by
  simp [hAux]

theorem hσ_high {n : ℕ} (h : ¬ n ≤ hNT G S K + hNY G S K) :
    hσ G ord S K tiles n = true ↔ ∃ k < (hGroups G ord S K).length, ∃ a, 1 ≤ a ∧
      a ≤ ((hGroups G ord S K).getD k []).length - 1 ∧
      n = hNT G S K + hNY G S K + ((hAux G ord S K).take k).sum + a ∧
      ∃ b, 1 ≤ b ∧ b ≤ a ∧
        LitTrue (hσ0 G S K tiles) (((hGroups G ord S K).getD k []).getD (b - 1) 0) := by
  unfold hσ; rw [if_neg h]; simp only [decide_eq_true_eq]

theorem litTrue_low {l : ℤ} (h : l.natAbs ≤ hNT G S K + hNY G S K) :
    LitTrue (hσ G ord S K tiles) l ↔ LitTrue (hσ0 G S K tiles) l := by
  simp only [LitTrue, hσ_low h]

theorem sat_C (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) (hord : ∀ c g, (ord c g).Perm g) :
    AllSat (hσ G ord S K tiles) (hClC G ord S K) := by
  intro C hC
  simp only [hClC, List.mem_flatMap] at hC
  obtain ⟨gb, hgb, hC⟩ := hC
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hgb
  rw [List.getElem_zip] at hC
  simp only at hC
  have hkG : k < (hGroups G ord S K).length := by
    have := hk; rw [List.length_zip] at this; omega
  have hkB : k < (hBases G ord S K).length := by
    have := hk; rw [List.length_zip] at this; omega
  have hbase : (hBases G ord S K)[k] = hNT G S K + hNY G S K + ((hAux G ord S K).take k).sum := by
    simp [hBases]
  rw [hbase] at hC
  set g := (hGroups G ord S K)[k] with hg
  have hgc : ∃ c, g = ord c (hGroup0 G S K c) := by
    refine ⟨(hCoverCells G S K)[k]'(by simpa [hGroups] using hkG), ?_⟩
    simp [g, hGroups]
  obtain ⟨c, hgc⟩ := hgc
  have hperm := hord c (hGroup0 G S K c)
  rw [← hgc] at hperm
  have hnodup : g.Nodup := hperm.nodup_iff.mpr (hGroup0_nodup c)
  have hmemg : ∀ x, x ∈ g ↔ x ∈ hGroup0 G S K c := fun x => hperm.mem_iff
  have hlow : ∀ x ∈ g, x.natAbs ≤ hNT G S K ∧ 0 < x := by
    intro x hx
    obtain ⟨i, hi, _, rfl⟩ := mem_hGroup0.mp ((hmemg x).mp hx)
    simp only [Int.natAbs_natCast]; omega
  have hgetD : ∀ b, 1 ≤ b → b ≤ g.length → g.getD (b - 1) 0 ∈ g := by
    intro b h1 h2; rw [getD_of_lt (by omega)]; exact List.getElem_mem _
  have hgk : (hGroups G ord S K).getD k [] = g := getD_of_lt hkG
  refine amo_sat _ g _ ?_ ?_ ?_ C hC
  · intro l hl; have := (hlow l hl).2; omega
  · intro a h1 h2
    rw [hσ_high (by omega)]
    constructor
    · rintro ⟨k', hk', a', h1', h2', heq, b, hb1, hb2, hb⟩
      have hkA : k < (hAux G ord S K).length := by rw [length_hAux]; exact hkG
      have hkA' : k' < (hAux G ord S K).length := by rw [length_hAux]; exact hk'
      have hAk : (hAux G ord S K)[k] = g.length - 1 := by simp [hAux, g]
      have hAk' : (hAux G ord S K)[k'] = ((hGroups G ord S K).getD k' []).length - 1 := by
        rw [getD_of_lt hk']; simp [hAux]
      obtain ⟨rfl, rfl⟩ := slot_unique (hAux G ord S K) hkA hkA' h1 (by omega) h1' (by omega)
        (by omega)
      rw [hgk] at hb
      refine ⟨b, hb1, hb2, ?_⟩
      have hm := hgetD b hb1 (by omega)
      rw [litTrue_low (by have := (hlow _ hm).1; omega)]; exact hb
    · rintro ⟨b, hb1, hb2, hb⟩
      refine ⟨k, hkG, a, h1, ?_, rfl, b, hb1, hb2, ?_⟩
      · rw [hgk]; exact h2
      · have hm := hgetD b hb1 (by omega)
        rw [hgk, ← litTrue_low (ord := ord) (by have := (hlow _ hm).1; omega)]; exact hb
  · intro b b' h1 h2 h1' h2' hb hb'
    have hm := hgetD b h1 h2
    have hm' := hgetD b' h1' h2'
    have heq := hGroup0_amo hG hc ((hmemg _).mp hm) ((hmemg _).mp hm') hb hb'
    rw [getD_of_lt (by omega), getD_of_lt (by omega)] at heq
    have := (hnodup.getElem_inj_iff).mp heq
    omega



variable {G : Grid} {ord : Cell → List ℤ → List ℤ} {S : List Cell} {K : ℕ} {tiles : Tiles}

theorem hYVar_some {cj : Cell × ℕ} (h : cj ∈ hYPairs G S K) :
    hYVar G S K cj.1 cj.2 = some (hY G S K cj.1 cj.2) := by
  obtain ⟨i, hi⟩ := posOf_isSome h
  simp [hY, hYVar, hi]

theorem hTVar_some {p : List Cell} {j : ℕ} {v : ℤ} (h : hTVar G S K p j = some v) :
    (p, j) ∈ hTPairs G S K ∧ v = hT G S K p j := by
  unfold hTVar at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨mem_of_posOf hi, ?_⟩
  simp [hT, hTVar, hi]

theorem sat_H (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) {M : ℕ} (hM : M ≤ K)
    {blocks : List HoleBlock} (hb : ∀ b ∈ blocks, b.Valid G M)
    (hd : ∀ j, 1 ≤ j → j ≤ M → ¬ HasHole G (cover tiles j)) :
    AllSat (hσ G ord S K tiles) (hClH G S K blocks) := by
  intro C hC
  simp only [hClH, List.mem_filterMap] at hC
  obtain ⟨b, hbm, hC⟩ := hC
  obtain ⟨hl1, hl2, hne, hcell, hencl, hbd⟩ := hb b hbm
  unfold hHoleClause at hC
  simp only at hC
  split_ifs at hC with h1 h2
  simp only [Option.some.injEq] at hC
  subst hC
  by_contra hfalse
  push_neg at hfalse
  -- the enclosing cells lie in `P_j`
  have hE : ∀ e ∈ b.enclosing, ∀ d ∈ e.2, d ∈ cover tiles b.level := by
    intro e he d hde
    have h2' := h2
    simp only [List.any_eq_true, List.mem_map, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Option.isNone_iff_eq_none, not_exists, not_and] at h2'
    by_cases hz : e.1 = 0 ∧ sortCells e.2 = sortCells S
    · have hdS : d ∈ S := by
        have : d ∈ sortCells e.2 := by simpa using hde
        rw [hz.2] at this; simpa using this
      exact cover_mono (Nat.zero_le _) ((cover_zero hc).mpr hdS)
    · have hsome : hTVar G S K (sortCells e.2) e.1 ≠ none :=
        fun hn => h2' _ ⟨e, he, rfl⟩ (fun h0 hS => hz ⟨h0, hS⟩) hn
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hsome
      obtain ⟨hpT, rfl⟩ := hTVar_some hv
      have hlit := hfalse (-(hT G S K (sortCells e.2) e.1)) (by
        simp only [List.mem_append, List.mem_filterMap, List.mem_map]
        left
        exact ⟨(e.1, sortCells e.2), ⟨e, he, rfl⟩, by simp only [hv, Option.map_some]⟩)
      rw [lit_neg_hT (pj := (sortCells e.2, e.1)) hpT] at hlit
      push_neg at hlit
      exact mem_cover_of (real_tile hlit) (hencl e he) (by simpa using hde)
  -- the hole cells are outside `P_j`
  have hH : ∀ c ∈ b.hole, c ∉ cover tiles b.level := by
    intro c hcH hcP
    have hcS : c ∉ S := by
      intro hcS
      apply h1
      simp only [List.any_eq_true, decide_eq_true_eq]
      exact ⟨c, hcH, by simpa using hcS⟩
    have hR' := cover_sub_hR (S := S) hG hc (by omega) hcP
    have hy : (c, b.level) ∈ hYPairs G S K := mem_hYPairs.mpr ⟨⟨hl1, by omega⟩, hR', hcS⟩
    have hlit := hfalse (hY G S K c b.level) (by
      simp only [List.mem_append, List.mem_filterMap]
      right
      exact ⟨c, by simpa using hcH, hYVar_some hy⟩)
    exact hlit ((lit_hY hy).mpr hcP)
  exact hd b.level hl1 hl2 (hasHole_of_trapped hG _ b.hole hne hcell hH (fun c hc d hcd hdH => by
    obtain ⟨e, he, hde⟩ := hbd c hc d hcd hdH
    exact hE e he d hde))



theorem sat_of_corona (hG : GridOK G) (ord : Cell → List ℤ → List ℤ)
    (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K M : ℕ) (hM : M ≤ K) (blocks : List HoleBlock)
    (hb : ∀ b ∈ blocks, b.Valid G M) (tiles : Tiles) (hc : IsCorona G S.toFinset K tiles)
    (hd : ∀ j, 1 ≤ j → j ≤ M → ¬ HasHole G (cover tiles j)) :
    Satisfiable (cnfOrd G ord S K blocks) := by
  refine ⟨hσ G ord S K tiles, ?_⟩
  intro C hC
  simp only [cnfOrd_eq_cnfOrdP, cnfOrdP, List.mem_append] at hC
  rcases hC with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact sat_F hG hc C h
  · rw [clBad_nil hG hc] at h; simp at h
  · exact sat_Y1 C h
  · exact sat_Y2 hG hc C h
  · exact sat_B hG hc C h
  · exact sat_C hG hc hord C h
  · exact sat_D hG hc C h
  · exact sat_E hG hc C h
  · exact sat_H hG hc hM hb hd C h

/-- **Hh soundness on every grid with `GridOK`, for every input order of the counters.** -/
theorem hh_sound_grid (hG : GridOK G) (ord : Cell → List ℤ → List ℤ)
    (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K : ℕ) (blocks : List HoleBlock)
    (hblocks : ∀ b ∈ blocks, b.Valid G (K - 1))
    (hunsat : ¬ Satisfiable (cnfOrd G ord S K blocks)) :
    ¬ ∃ tiles : Tiles, IsCoronaHh G S.toFinset K tiles := by
  rintro ⟨tiles, hc, hd⟩
  exact hunsat (sat_of_corona hG ord hord S K (K - 1) (by omega) blocks hblocks tiles hc
    (fun j _ h2 => (hd j (by omega)).2.1))

/-- **Hc soundness on every grid with `GridOK`, for every input order of the counters.** -/
theorem hc_sound_grid (hG : GridOK G) (ord : Cell → List ℤ → List ℤ)
    (hord : ∀ c g, (ord c g).Perm g)
    (S : List Cell) (K : ℕ) (blocks : List HoleBlock)
    (hblocks : ∀ b ∈ blocks, b.Valid G K)
    (hunsat : ¬ Satisfiable (cnfOrd G ord S K blocks)) :
    ¬ ∃ tiles : Tiles, IsCoronaHc G S.toFinset K tiles := by
  rintro ⟨tiles, hc, hd⟩
  exact hunsat (sat_of_corona hG ord hord S K K le_rfl blocks hblocks tiles hc
    (fun j _ h2 => (hd j h2).2.1))

end HeeschProof
