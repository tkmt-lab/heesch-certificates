import Heesch.Square.Cand

/-!
# Heesch CNF soundness (polyominoes), the CNF with named parts and a free input order for (C)

`cnfOrd ord S K blocks` is `cnf S K blocks` (of `Heesch.Square.Spec`, the challenge's
definition) with every `let` made a named definition, and with one change: the input list of
the sequential "at most one" counter of cell `c` is `ord c g` instead of `g`. With
`ord = fun _ g => g` it is `cnf` itself (`cnf_eq_cnfOrd`, by `rfl`). The soundness proof is
done for every `ord` with `ord c g` a permutation of `g`.
-/

namespace HeeschSquareProof

open HeeschSquare

section Parts

variable (ord : Cell → List ℤ → List ℤ) (S : List Cell) (K : ℕ)

/-- `R_j` computed from the candidates. -/
def hR (j : ℕ) : List Cell :=
  ((List.range (K + 2)).map (reachOf (sortCells S) (candidates S K))).getD j []

/-- The layers `1..K`. -/
def hLayers : List ℕ := (List.range K).map (· + 1)

/-- The pairs `(p, j)` of the variables `t[p,j]`. -/
def hTPairs : List (List Cell × ℕ) :=
  (candidates S K).flatMap fun pl => pl.2.map fun j => (pl.1, j)

/-- The number of `t` variables. -/
def hNT : ℕ := (hTPairs S K).length

/-- The pairs `(c, j)` of the variables `y[c,j]`. -/
def hYPairs : List (Cell × ℕ) :=
  (hLayers K).flatMap fun j =>
    ((hR S K j).filter fun c => decide (c ∉ sortCells S)).map fun c => (c, j)

/-- The number of `y` variables. -/
def hNY : ℕ := (hYPairs S K).length

/-- The variable `t[p,j]`, if any. -/
def hTVar (p : List Cell) (j : ℕ) : Option ℤ :=
  (posOf (p, j) (hTPairs S K)).map fun i => ((i + 1 : ℕ) : ℤ)

/-- The variable `y[c,j]`, if any. -/
def hYVar (c : Cell) (j : ℕ) : Option ℤ :=
  (posOf (c, j) (hYPairs S K)).map fun i => ((hNT S K + i + 1 : ℕ) : ℤ)

/-- The literal `t[p,j]` (`0` if there is no such variable). -/
def hT (p : List Cell) (j : ℕ) : ℤ := (hTVar S K p j).getD 0

/-- The literal `y[c,j]` (`0` if there is no such variable). -/
def hY (c : Cell) (j : ℕ) : ℤ := (hYVar S K c j).getD 0

/-- The cells of the candidates. -/
def hCoverCells : List Cell := sortCells ((candidates S K).map Prod.fst).flatten

/-- The inputs of the counter of cell `c`, in the order of `cnf`. -/
def hGroup0 (c : Cell) : List ℤ :=
  ((List.range (hNT S K)).filter fun i => decide (c ∈ ((hTPairs S K).getD i ([], 0)).1)).map
    fun i => ((i + 1 : ℕ) : ℤ)

/-- The counter inputs, reordered by `ord`. -/
def hGroups : List (List ℤ) := (hCoverCells S K).map fun c => ord c (hGroup0 S K c)

/-- Counter variables per group. -/
def hAux : List ℕ := (hGroups ord S K).map fun g => g.length - 1

/-- Counter bases. -/
def hBases : List ℕ :=
  (List.range (hGroups ord S K).length).map fun i =>
    hNT S K + hNY S K + ((hAux ord S K).take i).sum

/-- The fresh variable of (F). -/
def hVBad : ℤ := ((hNT S K + hNY S K + (hAux ord S K).sum + 1 : ℕ) : ℤ)

/-- The search box of (F). -/
def hBox : List Cell :=
  (intRange (((sortCells S).map Prod.fst).min?.getD 0 - K)
      (((sortCells S).map Prod.fst).max?.getD 0 + K)).flatMap fun a =>
    (intRange (((sortCells S).map Prod.snd).min?.getD 0 - K)
      (((sortCells S).map Prod.snd).max?.getD 0 + K)).map fun b => (a, b)

/-- The cells with `1 ≤ d(c) ≤ K`. -/
def hFCells : List Cell :=
  (hBox S K).filter fun c =>
    match dist (sortCells S) c with
    | some d => decide (1 ≤ d ∧ d ≤ K)
    | none => false

/-- Those of them in `R_{d(c)}`. -/
def hFOk : List Cell :=
  (hFCells S K).filter fun c => decide (c ∈ hR S K ((dist (sortCells S) c).getD 0))

def hClF : CNF := (hFOk S K).map fun c => [hY S K c ((dist (sortCells S) c).getD 0)]

def hClBad : CNF :=
  if (hFOk S K).length < (hFCells S K).length then [[hVBad ord S K], [-hVBad ord S K]] else []

def hClY1 : CNF :=
  ((List.range (K - 1)).map (· + 2)).flatMap fun j =>
    ((hR S K (j - 1)).filter fun c => decide (c ∉ sortCells S)).map fun c =>
      [-(hY S K c (j - 1)), hY S K c j]

def hClY2 : CNF :=
  (hLayers K).flatMap fun j =>
    ((hR S K j).filter fun c => decide (c ∉ sortCells S)).map fun c =>
      [-(hY S K c j)] ++ (if 2 ≤ j ∧ c ∈ hR S K (j - 1) then [hY S K c (j - 1)] else []) ++
        (((hTPairs S K).filter fun pj => decide (pj.2 = j ∧ c ∈ pj.1)).map fun pj =>
          hT S K pj.1 pj.2)

def hClB : CNF :=
  (hTPairs S K).flatMap fun pj => pj.1.map fun c => [-(hT S K pj.1 pj.2), hY S K c pj.2]

def hClC : CNF := ((hGroups ord S K).zip (hBases ord S K)).flatMap fun gb => amoClauses gb.1 gb.2

def hClD : CNF :=
  (hTPairs S K).flatMap fun pj =>
    if pj.2 < K then
      ((haloL pj.1).filter fun c => decide (c ∉ sortCells S)).map fun c =>
        [-(hT S K pj.1 pj.2)] ++ (if c ∈ hR S K (pj.2 + 1) then [hY S K c (pj.2 + 1)] else [])
    else []

def hClE : CNF :=
  (hTPairs S K).flatMap fun pj =>
    if 2 ≤ pj.2 ∧ meets (haloL pj.1) (sortCells S) = false then
      [[-(hT S K pj.1 pj.2)] ++
        ((haloL pj.1).filter fun c => decide (c ∈ hR S K (pj.2 - 1) ∧ c ∉ sortCells S)).map
          fun c => hY S K c (pj.2 - 1)]
    else []

/-- The hole clause of one block (`none` if it is dropped). -/
def hHoleClause (b : HoleBlock) : Option (List ℤ) :=
  let encl := b.enclosing.map fun e => (e.1, sortCells e.2)
  if b.hole.any (fun c => decide (c ∈ sortCells S)) then none
  else if encl.any (fun e => !(decide (e.1 = 0 ∧ e.2 = sortCells S)) &&
      (hTVar S K e.2 e.1).isNone) then none
  else some ((encl.filterMap fun e => (hTVar S K e.2 e.1).map (- ·)) ++
    (sortCells b.hole).filterMap fun c => hYVar S K c b.level)

def hClH (blocks : List HoleBlock) : CNF := blocks.filterMap (hHoleClause S K)

/-- `cnf` with the counter inputs of each cell reordered by `ord`. -/
def cnfOrd (blocks : List HoleBlock) : CNF :=
  hClF S K ++ hClBad ord S K ++ hClY1 S K ++ hClY2 S K ++ hClB S K ++ hClC ord S K ++
    hClD S K ++ hClE S K ++ hClH S K blocks

end Parts

/-- The challenge's CNF is the case `ord = id`. -/
theorem cnf_eq_cnfOrd (S : List Cell) (K : ℕ) (blocks : List HoleBlock) :
    cnf S K blocks = cnfOrd (fun _ g => g) S K blocks := rfl

end HeeschSquareProof
