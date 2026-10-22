import Heesch.Cand

/-!
# Heesch CNF soundness on three grids: the CNF with named parts, and the assignment from a corona

`cnfOrdP G ord S K blocks` is the challenge's `cnfOrd G ord S K blocks` with every `let` made a
named definition (`cnfOrd_eq_cnfOrdP`, by `rfl`). The assignment `hσ G ord S K tiles`:
`t[p,j]` (at the first occurrence of `(p, j)`) is true iff `(j, p.toFinset) ∈ tiles`; `y[c,j]`
iff `c ∈ P_j`; the counter variable `s_a` of a group iff one of its first `a` inputs is true.
This is `Heesch.Square.Ord` and `Heesch.Square.Assign` made generic over the grid.
-/

namespace HeeschProof

open Heesch

section Parts

variable (G : Grid) (ord : Cell → List ℤ → List ℤ) (S : List Cell) (K : ℕ)

/-- `R_j` computed from the candidates. -/
def hR (j : ℕ) : List Cell :=
  ((List.range (K + 2)).map (reachOf (sortCells S) (candidates G S K))).getD j []

/-- The layers `1..K`. -/
def hLayers : List ℕ := (List.range K).map (· + 1)

/-- The pairs `(p, j)` of the variables `t[p,j]`. -/
def hTPairs : List (List Cell × ℕ) :=
  (candidates G S K).flatMap fun pl => pl.2.map fun j => (pl.1, j)

/-- The number of `t` variables. -/
def hNT : ℕ := (hTPairs G S K).length

/-- The pairs `(c, j)` of the variables `y[c,j]`. -/
def hYPairs : List (Cell × ℕ) :=
  (hLayers K).flatMap fun j =>
    ((hR G S K j).filter fun c => decide (c ∉ sortCells S)).map fun c => (c, j)

/-- The number of `y` variables. -/
def hNY : ℕ := (hYPairs G S K).length

/-- The variable `t[p,j]`, if any. -/
def hTVar (p : List Cell) (j : ℕ) : Option ℤ :=
  (posOf (p, j) (hTPairs G S K)).map fun i => ((i + 1 : ℕ) : ℤ)

/-- The variable `y[c,j]`, if any. -/
def hYVar (c : Cell) (j : ℕ) : Option ℤ :=
  (posOf (c, j) (hYPairs G S K)).map fun i => ((hNT G S K + i + 1 : ℕ) : ℤ)

/-- The literal `t[p,j]` (`0` if there is no such variable). -/
def hT (p : List Cell) (j : ℕ) : ℤ := (hTVar G S K p j).getD 0

/-- The literal `y[c,j]` (`0` if there is no such variable). -/
def hY (c : Cell) (j : ℕ) : ℤ := (hYVar G S K c j).getD 0

/-- The cells of the candidates. -/
def hCoverCells : List Cell := sortCells ((candidates G S K).map Prod.fst).flatten

/-- The inputs of the counter of cell `c`, in the order of `cnf`. -/
def hGroup0 (c : Cell) : List ℤ :=
  ((List.range (hNT G S K)).filter fun i => decide (c ∈ ((hTPairs G S K).getD i ([], 0)).1)).map
    fun i => ((i + 1 : ℕ) : ℤ)

/-- The counter inputs, reordered by `ord`. -/
def hGroups : List (List ℤ) := (hCoverCells G S K).map fun c => ord c (hGroup0 G S K c)

/-- Counter variables per group. -/
def hAux : List ℕ := (hGroups G ord S K).map fun g => g.length - 1

/-- Counter bases. -/
def hBases : List ℕ :=
  (List.range (hGroups G ord S K).length).map fun i =>
    hNT G S K + hNY G S K + ((hAux G ord S K).take i).sum

/-- The fresh variable of (F). -/
def hVBad : ℤ := ((hNT G S K + hNY G S K + (hAux G ord S K).sum + 1 : ℕ) : ℤ)

/-- The search box of (F). -/
def hBox : List Cell := G.box (sortCells S) K

/-- The cells with `1 ≤ d(c) ≤ K`. -/
def hFCells : List Cell :=
  (hBox G S K).filter fun c =>
    match G.dist (sortCells S) c with
    | some d => decide (1 ≤ d ∧ d ≤ K)
    | none => false

/-- Those of them in `R_{d(c)}`. -/
def hFOk : List Cell :=
  (hFCells G S K).filter fun c => decide (c ∈ hR G S K ((G.dist (sortCells S) c).getD 0))

def hClF : CNF := (hFOk G S K).map fun c => [hY G S K c ((G.dist (sortCells S) c).getD 0)]

def hClBad : CNF :=
  if (hFOk G S K).length < (hFCells G S K).length then [[hVBad G ord S K], [-hVBad G ord S K]] else []

def hClY1 : CNF :=
  ((List.range (K - 1)).map (· + 2)).flatMap fun j =>
    ((hR G S K (j - 1)).filter fun c => decide (c ∉ sortCells S)).map fun c =>
      [-(hY G S K c (j - 1)), hY G S K c j]

def hClY2 : CNF :=
  (hLayers K).flatMap fun j =>
    ((hR G S K j).filter fun c => decide (c ∉ sortCells S)).map fun c =>
      [-(hY G S K c j)] ++ (if 2 ≤ j ∧ c ∈ hR G S K (j - 1) then [hY G S K c (j - 1)] else []) ++
        (((hTPairs G S K).filter fun pj => decide (pj.2 = j ∧ c ∈ pj.1)).map fun pj =>
          hT G S K pj.1 pj.2)

def hClB : CNF :=
  (hTPairs G S K).flatMap fun pj => pj.1.map fun c => [-(hT G S K pj.1 pj.2), hY G S K c pj.2]

def hClC : CNF := ((hGroups G ord S K).zip (hBases G ord S K)).flatMap fun gb => amoClauses gb.1 gb.2

def hClD : CNF :=
  (hTPairs G S K).flatMap fun pj =>
    if pj.2 < K then
      ((haloL G pj.1).filter fun c => decide (c ∉ sortCells S)).map fun c =>
        [-(hT G S K pj.1 pj.2)] ++ (if c ∈ hR G S K (pj.2 + 1) then [hY G S K c (pj.2 + 1)] else [])
    else []

def hClE : CNF :=
  (hTPairs G S K).flatMap fun pj =>
    if 2 ≤ pj.2 ∧ meets (haloL G pj.1) (sortCells S) = false then
      [[-(hT G S K pj.1 pj.2)] ++
        ((haloL G pj.1).filter fun c => decide (c ∈ hR G S K (pj.2 - 1) ∧ c ∉ sortCells S)).map
          fun c => hY G S K c (pj.2 - 1)]
    else []

/-- The hole clause of one block (`none` if it is dropped). -/
def hHoleClause (b : HoleBlock) : Option (List ℤ) :=
  let encl := b.enclosing.map fun e => (e.1, sortCells e.2)
  if b.hole.any (fun c => decide (c ∈ sortCells S)) then none
  else if encl.any (fun e => !(decide (e.1 = 0 ∧ e.2 = sortCells S)) &&
      (hTVar G S K e.2 e.1).isNone) then none
  else some ((encl.filterMap fun e => (hTVar G S K e.2 e.1).map (- ·)) ++
    (sortCells b.hole).filterMap fun c => hYVar G S K c b.level)

def hClH (blocks : List HoleBlock) : CNF := blocks.filterMap (hHoleClause G S K)

/-- `cnf` with the counter inputs of each cell reordered by `ord`. -/
def cnfOrdP (blocks : List HoleBlock) : CNF :=
  hClF G S K ++ hClBad G ord S K ++ hClY1 G S K ++ hClY2 G S K ++ hClB G S K ++ hClC G ord S K ++
    hClD G S K ++ hClE G S K ++ hClH G S K blocks

end Parts

/-- The challenge's `cnfOrd` (with `let`s) is `cnfOrdP` (with named parts). -/
theorem cnfOrd_eq_cnfOrdP (G : Grid) (ord : Cell → List ℤ → List ℤ) (S : List Cell) (K : ℕ)
    (blocks : List HoleBlock) : cnfOrd G ord S K blocks = cnfOrdP G ord S K blocks := rfl

/-! ## The assignment built from a corona -/

/-- The pair `(p, j)` is a real tile. -/
def RealTile (tiles : Tiles) (pj : List Cell × ℕ) : Prop := (pj.2, pj.1.toFinset) ∈ tiles

section Sigma

variable (G : Grid) (ord : Cell → List ℤ → List ℤ) (S : List Cell) (K : ℕ) (tiles : Tiles)

open Classical in
/-- The assignment on the `t` and `y` variables. -/
noncomputable def hσ0 (n : ℕ) : Bool :=
  if n ≤ hNT G S K then
    decide (RealTile tiles ((hTPairs G S K).getD (n - 1) ([], 0)) ∧
      posOf ((hTPairs G S K).getD (n - 1) ([], 0)) (hTPairs G S K) = some (n - 1))
  else
    decide (((hYPairs G S K).getD (n - hNT G S K - 1) ((0, 0), 0)).1 ∈
      cover tiles ((hYPairs G S K).getD (n - hNT G S K - 1) ((0, 0), 0)).2)

open Classical in
/-- The full assignment: counter variables after the `t` and `y` variables. -/
noncomputable def hσ (n : ℕ) : Bool :=
  if n ≤ hNT G S K + hNY G S K then hσ0 G S K tiles n
  else decide (∃ k < (hGroups G ord S K).length, ∃ a, 1 ≤ a ∧
      a ≤ ((hGroups G ord S K).getD k []).length - 1 ∧
      n = hNT G S K + hNY G S K + ((hAux G ord S K).take k).sum + a ∧
      ∃ b, 1 ≤ b ∧ b ≤ a ∧ LitTrue (hσ0 G S K tiles) (((hGroups G ord S K).getD k []).getD (b - 1) 0))

end Sigma

variable {G : Grid} {ord : Cell → List ℤ → List ℤ} {S : List Cell} {K : ℕ} {tiles : Tiles}

/-! ## Literals -/

theorem litTrue_pos {σ : ℕ → Bool} {n : ℕ} (h : 0 < n) : LitTrue σ (n : ℤ) ↔ σ n = true := by
  simp only [LitTrue, Int.natAbs_natCast]
  constructor
  · rintro (⟨_, h'⟩ | ⟨h', _⟩)
    · exact h'
    · omega
  · intro h'; exact Or.inl ⟨by omega, h'⟩

theorem litTrue_neg {σ : ℕ → Bool} {n : ℕ} (h : 0 < n) :
    LitTrue σ (-(n : ℤ)) ↔ σ n = false := by
  simp only [LitTrue, Int.natAbs_neg, Int.natAbs_natCast]
  constructor
  · rintro (⟨h', _⟩ | ⟨_, h'⟩)
    · omega
    · exact h'
  · intro h'; exact Or.inr ⟨by omega, h'⟩

/-! ## The variable ranges -/

theorem hR_eq {j : ℕ} (h : j < K + 2) :
    hR G S K j = reachOf (sortCells S) (candidates G S K) j := getD_range_map _ _ h

theorem mem_hTPairs {pj : List Cell × ℕ} :
    pj ∈ hTPairs G S K ↔ ∃ pl ∈ candidates G S K, pl.1 = pj.1 ∧ pj.2 ∈ pl.2 := by
  obtain ⟨p, j⟩ := pj
  simp only [hTPairs, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨pl, hpl, j', hj', rfl, rfl⟩; exact ⟨pl, hpl, rfl, hj'⟩
  · rintro ⟨pl, hpl, rfl, hj⟩; exact ⟨pl, hpl, j, hj, rfl, rfl⟩

theorem mem_hYPairs {cj : Cell × ℕ} :
    cj ∈ hYPairs G S K ↔ (1 ≤ cj.2 ∧ cj.2 ≤ K) ∧ cj.1 ∈ hR G S K cj.2 ∧ cj.1 ∉ S := by
  obtain ⟨c, j⟩ := cj
  simp only [hYPairs, hLayers, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_filter,
    decide_eq_true_eq, mem_sortCells, Prod.mk.injEq]
  constructor
  · rintro ⟨j', ⟨i, hi, rfl⟩, c', ⟨hc', hc'S⟩, rfl, rfl⟩; exact ⟨⟨by omega, by omega⟩, hc', hc'S⟩
  · rintro ⟨⟨h1, h2⟩, hc, hcS⟩; exact ⟨j, ⟨j - 1, by omega, by omega⟩, c, ⟨hc, hcS⟩, rfl, rfl⟩

theorem tPairs_props (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) {pj : List Cell × ℕ}
    (h : pj ∈ hTPairs G S K) :
    IsSorted pj.1 ∧ (∀ c ∈ pj.1, c ∉ S) ∧ 1 ≤ pj.2 ∧ pj.2 ≤ K ∧ ∀ c ∈ pj.1, c ∈ hR G S K pj.2 := by
  obtain ⟨pl, hpl, h1, h2⟩ := mem_hTPairs.mp h
  obtain ⟨htc, hl⟩ := (candidates_good hG hc).1 pl hpl
  have hb := hl _ h2
  refine ⟨h1 ▸ touchingCopies_sorted htc, ?_, hb.1, hb.2, ?_⟩
  · intro c hcp; have := touchingCopies_disj htc c (h1 ▸ hcp); simpa using this
  · intro c hcp
    rw [hR_eq (by omega), mem_reachOf]
    exact Or.inr ⟨pl, hpl, ⟨pj.2, h2, le_refl _⟩, h1 ▸ hcp⟩

theorem real_mem_tPairs (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) {u : ℕ × Finset Cell}
    (hu : u ∈ tiles) (h1 : 1 ≤ u.1) :
    ∃ p, (p, u.1) ∈ hTPairs G S K ∧ (∀ c, c ∈ p ↔ c ∈ u.2) ∧ RealTile tiles (p, u.1) := by
  obtain ⟨pl, hpl, hmem, hupl⟩ := (candidates_good hG hc).2 u hu h1
  refine ⟨pl.1, mem_hTPairs.mpr ⟨pl, hpl, rfl, hupl⟩, hmem, ?_⟩
  have : pl.1.toFinset = u.2 := by ext c; simp [hmem c]
  change (u.1, pl.1.toFinset) ∈ tiles
  rw [this]; exact hu

theorem cover_sub_hR (hG : GridOK G) (hc : IsCorona G S.toFinset K tiles) {j : ℕ} (hj : j < K + 2) {c : Cell}
    (h : c ∈ cover tiles j) : c ∈ hR G S K j := by
  rw [hR_eq hj]; exact cover_sub_reachOf hc (candidates_good hG hc) h

theorem hR_mono {j j' : ℕ} (h : j ≤ j') (hj' : j' < K + 2) {c : Cell} (hc : c ∈ hR G S K j) :
    c ∈ hR G S K j' := by
  rw [hR_eq (by omega)] at hc; rw [hR_eq hj']; exact reachOf_mono h hc

/-! ## The literals `hT`, `hY` -/

theorem hσ_low {n : ℕ} (h : n ≤ hNT G S K + hNY G S K) : hσ G ord S K tiles n = hσ0 G S K tiles n := by
  unfold hσ; rw [if_pos h]

theorem hT_eq {pj : List Cell × ℕ} (h : pj ∈ hTPairs G S K) :
    ∃ i, posOf pj (hTPairs G S K) = some i ∧ hT G S K pj.1 pj.2 = ((i + 1 : ℕ) : ℤ) := by
  obtain ⟨i, hi⟩ := posOf_isSome h
  refine ⟨i, hi, ?_⟩
  simp [hT, hTVar, hi]

theorem hσ_t {pj : List Cell × ℕ} {i : ℕ} (hi : posOf pj (hTPairs G S K) = some i) :
    hσ G ord S K tiles (i + 1) = true ↔ RealTile tiles pj := by
  have hlt := posOf_lt hi
  have hget : (hTPairs G S K).getD i ([], 0) = pj := posOf_getD hi
  rw [hσ_low (by unfold hNT; omega)]
  unfold hσ0
  rw [if_pos (by unfold hNT; omega)]
  simp only [Nat.add_sub_cancel, hget, hi, and_true, decide_eq_true_eq]

theorem lit_hT {pj : List Cell × ℕ} (h : pj ∈ hTPairs G S K) :
    LitTrue (hσ G ord S K tiles) (hT G S K pj.1 pj.2) ↔ RealTile tiles pj := by
  obtain ⟨i, hi, he⟩ := hT_eq h
  rw [he, litTrue_pos (by omega), hσ_t hi]

theorem lit_neg_hT {pj : List Cell × ℕ} (h : pj ∈ hTPairs G S K) :
    LitTrue (hσ G ord S K tiles) (-(hT G S K pj.1 pj.2)) ↔ ¬ RealTile tiles pj := by
  obtain ⟨i, hi, he⟩ := hT_eq h
  rw [he, litTrue_neg (by omega), ← hσ_t (ord := ord) hi]; simp

theorem hY_eq {cj : Cell × ℕ} (h : cj ∈ hYPairs G S K) :
    ∃ i, posOf cj (hYPairs G S K) = some i ∧ hY G S K cj.1 cj.2 = ((hNT G S K + i + 1 : ℕ) : ℤ) := by
  obtain ⟨i, hi⟩ := posOf_isSome h
  refine ⟨i, hi, ?_⟩
  simp [hY, hYVar, hi]

theorem hσ_y {cj : Cell × ℕ} {i : ℕ} (hi : posOf cj (hYPairs G S K) = some i) :
    hσ G ord S K tiles (hNT G S K + i + 1) = true ↔ cj.1 ∈ cover tiles cj.2 := by
  have hlt := posOf_lt hi
  have hget : (hYPairs G S K).getD i ((0, 0), 0) = cj := posOf_getD hi
  rw [hσ_low (by unfold hNY; omega)]
  unfold hσ0
  rw [if_neg (by omega)]
  have : hNT G S K + i + 1 - hNT G S K - 1 = i := by omega
  simp only [this, hget, decide_eq_true_eq]

theorem lit_hY {cj : Cell × ℕ} (h : cj ∈ hYPairs G S K) :
    LitTrue (hσ G ord S K tiles) (hY G S K cj.1 cj.2) ↔ cj.1 ∈ cover tiles cj.2 := by
  obtain ⟨i, hi, he⟩ := hY_eq h
  rw [he, litTrue_pos (by omega), hσ_y hi]

theorem lit_neg_hY {cj : Cell × ℕ} (h : cj ∈ hYPairs G S K) :
    LitTrue (hσ G ord S K tiles) (-(hY G S K cj.1 cj.2)) ↔ cj.1 ∉ cover tiles cj.2 := by
  obtain ⟨i, hi, he⟩ := hY_eq h
  rw [he, litTrue_neg (by omega), ← hσ_y (ord := ord) hi]; simp

end HeeschProof
