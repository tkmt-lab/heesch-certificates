# Definitions, encoding and file formats

This document is written so that a reader can implement a witness checker and an independent
encoding (or audit every clause of a CNF) without reading the code. Section numbers §1–§5 are
the ones cited in the Lean statement (`formal/Heesch/Challenge.lean`) and in the code comments.
The article (Sections 3 and 4) states the same definitions; where the two differ in wording, the
article is the reference for the mathematics and this file for the record formats.

## 1. Definitions (polyominoes)

- **Cell**: an integer pair `(x, y)`, the unit square `[x, x+1] × [y, y+1]`. Coordinates are those
  of Kaplan's data files.
- **Shape S**: a finite set of cells (first line of a shape in Kaplan's file, `x1 y1 x2 y2 …`).
- **Congruent copy**: `M·S + v` with `M` one of the 8 matrices with entries −1, 0, 1 (4 rotations,
  4 reflections) and `v` an integer vector.
- **Touching neighbours** `N8(c)`: the 8 cells sharing at least a point with `c`.
- **Edge neighbours** `N4(c)`: the 4 cells sharing an edge (used only to find holes).
- **Halo**: for a set of cells X, `Halo(X) = { c ∉ X : N8(c) ∩ X ≠ ∅ }`.
- **k-corona** (Kaplan 2022, Section 2.1): a set of copies, each with a layer number in `0..k`, such that
  - (P0) layer 0 consists of S itself (in the file's coordinates) only;
  - (P1) copies are pairwise disjoint (as cell sets);
  - (P2) writing `P_j` for the union of the copies of layer `≤ j`: `Halo(P_j) ⊆ P_{j+1}` for `j < k`;
  - (P3) every copy of layer `j ≥ 1` touches `P_{j-1}` (one of its cells lies in `Halo(P_{j-1})`);
  - (D) disc condition: `P_0, …, P_{k-1}` are closed discs. For **Hc**, `P_k` is a disc too; for
    **Hh**, `P_k` may have holes.
- **Hole** of P: a component, under `N4`, of the complement of P that is bounded.
- **Disc test** (a finite union of cells is a closed disc iff): (a) the cells are `N4`-connected,
  (b) there is no hole, (c) there is no pinch vertex (a vertex whose four cells are occupied in
  exactly the two diagonal positions). Under (P2)(P3), (a) and (c) follow from (b) (§5); the
  checkers test all three.
- **Heesch numbers**: `Hc` (`Hh`) is the largest k for which a k-corona in the Hc (Hh) sense exists.

### 1.1 Polyhexes and polyiamonds (Kaplan 2022, Section 4)

- **Polyhexes**: the cell `(x, y)` is the regular hexagon with centre `x·v + y·w`, `v = (1, 0)`,
  `w = (1/2, √3/2)`. Touching neighbours = edge neighbours = the 6 offsets `(±1, 0), (0, ±1), (1, −1), (−1, 1)`.
  The 12 orientations are `A^i B^j` with `A = [[0, −1], [1, 1]]` (rotation by 60°) and
  `B = [[1, 1], [0, −1]]` (reflection in the v axis); a matrix `[[a, b], [c, d]]` acts by
  `(x, y) ↦ (a x + b y, c x + d y)`. Translations are integer vectors. Three hexagons meet at each
  vertex and every two of them share an edge, so there are no pinch vertices.
- **Polyiamonds**: the same coordinates; `x ≡ y ≡ 0 (mod 3)` is a "black" triangle and
  `x ≡ y ≡ 1 (mod 3)` a "grey" triangle (the point is its centroid); other points are not cells.
  Vertices: black `(x, y)` has `(x−1, y+2), (x−1, y−1), (x+2, y−1)`, grey `(x, y)` has
  `(x+1, y−2), (x+1, y+1), (x−2, y+1)` (vertices are the points with `x ≡ y ≡ 2 (mod 3)`).
  **Touching** = sharing at least one vertex (12 cells), **edge neighbours** = sharing two vertices
  (3 cells). The 12 orientations are the hexagon matrices M, each with a small offset u such that
  `x ↦ Mx + u` maps the triangle grid to itself (vertices to vertices); translations are vectors in
  `3ℤ²` (colour-preserving). A pinch vertex is a vertex around which the occupied triangles, in angular
  order among the six, form two or more separate runs.
- Holes, halos, (P0)–(P3) and (D) are as for squares, with these neighbourhoods.

## 2. Witness files (lower bounds)

`witnesses/<family>/<Kaplan file name>.jsonl`, `family ∈ {omino, hex, iamond}`; one line per shape:

| Field | Meaning |
|---|---|
| `family` | `omino`, `hex` or `iamond` |
| `file`, `index` | Kaplan's file and the zero-based position of the shape in it (two lines per shape) |
| `shape` | the cells `[[x, y], …]` in the file's coordinates |
| `Hc`, `Hh` | the certified values |
| `witnesses` | list of witnesses |

A witness is `{"serves": ["Hc","Hh"] | ["Hh"] | ["Hc"], "k": k, "tiles": [[layer, [[x, y], …]], …]}`:
all copies with their layer and absolute cells. Layer 0 is the shape. If `serves` contains `Hc`,
`P_0..P_k` are discs; if only `Hh`, `P_k` may have holes (not listed; checkers find them).
A `k = 0` witness has the single layer-0 copy. When `Hc = Hh` one witness usually serves both;
when `Hc = Hh − 1` there are two.

**What a checker does** (no SAT): (P0)–(P3), congruence of every copy (each copy, normalized by
translation, equals one of the normalized images of S), layers `1..k` non-empty, (D) according to
`serves`, and `k` equal to the claimed value. Two checkers are included: `checkers/check_witness.py`
and `checkers/geometry.py`; neither imports the generator.

## 3. Certificate records (upper bounds)

`certificates/<family>/<Kaplan file stem>.jsonl`, one line per certificate:

| Field | Meaning |
|---|---|
| `name` | `<family>_<file stem>_<index:04d>_<cert_no>`; also the key of the file-comparison row |
| `family`, `file`, `index`, `cert_no`, `shape`, `Hc`, `Hh` | the shape and its values |
| `K`, `mode` | the claim "no K-layer corona": `mode = "Hh"` means (P0)–(P3) and `P_1..P_{K-1}` without holes, `"Hc"` also `P_K` without holes |
| `serves` | the values bounded (`K = Hh+1` bounds Hh and, as `Hc ≤ Hh`, Hc; `K = Hc+1` with mode Hc bounds Hc) |
| `blocks` | the hole clauses (H) of §4.4 as geometry: `{"level": j, "hole": [[x,y],…], "enclosing": [[layer, [[x,y],…]], …]}`; empty for all Hh certificates |
| `cnf` | SHA-256, bytes, variables, clauses of the DIMACS file (regenerated deterministically) |
| `solver`, `solver_options` | `cadical153` (CaDiCaL 1.5.3, binary DRAT), `glucose4` (Glucose 4.1, DRUP) or `lingeling` (text DRAT), through python-sat 1.9.dev17; options that switch off CaDiCaL's elim/subsume/vivify/probe were used for some large cases to stay within 1 GB |
| `proof` | SHA-256, bytes and format of the proof that was checked |
| `proof_from` | `first solve` if the proof was written by the solve that decided the value (only when no hole clause had been added), otherwise a fresh solve of the final CNF |
| `drat_trim` | drat-trim's result (`s VERIFIED`), wall time, verification time, and the memory cap of the run (MB) |

Regenerate and check: `python3 -B recheck_certificates.py --name <name>`. The CNF does not depend
on the solver; its SHA-256 must match. A proof re-written by the same solver build is expected to be
identical but this is not required: acceptance by drat-trim is the criterion.

## 4. Encoding (variables and clauses)

Input: shape S, number of layers K. Layer 0 is `T0 = S`.

### 4.1 Distance and static pruning (implied by the definitions, so no genuine corona is lost)
- `d(c)`: distance from `T0` in the touching graph (`0` on `T0`).
- **Lemma A**: in a k-corona and for `j ≤ k`, every cell with `d(c) ≤ j` lies in `P_j`
  (by (P2), `P_j ⊇ P_{j-1} ∪ Halo(P_{j-1})`; induction). Hence every cell of a layer-j copy has `d ≥ j`.
- Candidate copies p (copies of S disjoint from `T0`) and their layer interval `Λ(p) = [lo, hi]`:
  `R_0 = T0`; for `j = 1..K`, p is a candidate if `Halo(p)` meets `R_{j-1}` (for `j = 1`: meets `T0`);
  `hi = min(K, min_{c∈p} d(c))`, `lo` = the first such j; `R_j = R_{j-1} ∪` cells of the copies allowed at layer j.
  For `j < K`, `(p, j)` is kept only if `Halo(p) \ T0 ⊆ R_{j+1}`; `R` is recomputed and both tests are
  repeated until nothing changes. (A layer-j copy of a genuine corona always survives, by induction:
  the cells it touches lie in `R_{j-1}` and the copies covering its halo lie in `R_{j+1}`.)
- `R_j` over-approximates the cells coverable by layers `≤ j`.

### 4.2 Variables
- `t[p,j]` (`j ∈ Λ(p)`): copy p is used at layer j.
- `y[c,j]` (`c ∈ R_j \ T0`, `1 ≤ j ≤ K`): cell c is covered by copies of layer `≤ j`.
- Auxiliary `s[c,a]`: Sinz's sequential counter for "at most one" at cell c.
- If needed, one fresh variable for (F).

### 4.3 Clauses (the K-layer problem without hole conditions)
- (F) `y[c, d(c)]` for every c with `1 ≤ d(c) ≤ K` (Lemma A). If `c ∉ R_{d(c)}`, the clauses `v` and `¬v`
  with a fresh variable v are added instead.
- (Y1) `y[c,j-1] → y[c,j]`.
- (Y2) `y[c,j] → y[c,j-1] ∨ ⋁{ t[p,j] : c ∈ p, j ∈ Λ(p) }` (first disjunct omitted if `y[c,j-1]` does not exist).
- (B) `t[p,j] → y[c,j]` for `c ∈ p`.
- (C) for each cell c, at most one of `{ t[p,j] : c ∈ p, j ∈ Λ(p) }` (sequential counter:
  `x_1 → s_1`; `x_a → s_a`, `s_{a-1} → s_a`, `x_a → ¬s_{a-1}` for `1 < a < m`; `x_m → ¬s_{m-1}`).
  This gives (P1) and a single layer per copy. The order of the inputs is a free choice (`ord` in Lean).
- (D) for `j < K`: `t[p,j] → y[c,j+1]` for `c ∈ Halo(p) \ T0`; if `y[c,j+1]` does not exist, `¬t[p,j]`. This is (P2).
- (E) for `j ≥ 2` and p not touching `T0`: `t[p,j] → ⋁{ y[c,j-1] : c ∈ Halo(p) \ T0 }`. This is (P3);
  for `j = 1` it holds by construction.
- The CNF is satisfiable iff a K-layer patch satisfying (P0)–(P3) exists (without (D)). Hence
  **if it is unsatisfiable, there is no K-layer corona even with holes, and Hc, Hh ≤ K−1.** The Lean
  theorem proves the direction used here (corona ⇒ satisfying assignment), with hole blocks (§4.4).

### 4.4 Holes (Hc, and inner layers)
- After each satisfying assignment, holes of `P_j` are searched (`j = 1..K-1` in mode Hh, `j = 1..K` in mode Hc).
- If H is a hole of `P_j`, let E be the set of copies of layer `≤ j` that contain a cell of `∂H` (the edge
  neighbours of H outside H, all in `P_j`). The clause
  (H) `⋁_{(p,l) ∈ E} ¬t[p,l] ∨ ⋁_{c ∈ H} y[c,j]` is added and the problem solved again.
- **Soundness**: if all copies of E are used at their layers and no cell of H is covered by layers `≤ j`,
  then `∂H ⊆ P_j` and `H ∩ P_j = ∅`, so H contains a hole of `P_j`, contradicting the disc condition.
  Kaplan's hole clauses (2022, Section 3.2) contain only the negative literals; the positive literals added
  here keep assignments in which other copies fill H, so these clauses are weaker (safe).
- In the certificate records each (H) is stored as a block (§3). A block is valid when `1 ≤ j ≤` the maximal
  level, H is non-empty and consists of cells, every copy of E has layer `≤ j`, and every edge neighbour of H
  outside H lies in a copy of E (`HoleBlock.Valid` in Lean).
- An inner `P_j` (`j < K`) cannot have an empty hole (its halo is covered), but it can have a hole filled
  by copies of higher layers; Kaplan's definition forbids that too.

### 4.5 Computing the values
- Solve mode Hh for `K = 1, 2, …`; the first unsatisfiable K gives `Hh = K − 1`.
- If `Hh ≥ 1` and the Hh witness has no hole in `P_Hh`, then `Hc = Hh`. Otherwise solve mode Hc with `K = Hh`:
  satisfiable gives `Hc = Hh`, unsatisfiable `Hc = Hh − 1` (the Hh witness truncated to `Hh − 1` layers is the Hc witness).
- Upper-bound certificates: `K = Hh + 1` (mode Hh) and, if `Hc < Hh`, `K = Hc + 1` (mode Hc). The final CNF
  (base clauses and the (H) clauses) is solved again with proof output, unless the deciding solve already wrote one.

## 5. Why (a) and (c) of the disc test follow from (b)

Under (P2)(P3), `P_j` is connected (every copy touches the previous layer). Suppose at a vertex v only two
diagonal cells, in copies t1 and t2, belong to `P_j`. If either copy had layer `< j`, the two other cells at v
would lie in its halo and hence in `P_j`. So both have layer j and touch the previous layer away from v; a path
from t1 to t2 avoiding v, closed through v, separates the two outside cells, one of which lies in a hole. With no
hole there is no such vertex.

## 6. Other records in this packet

- `inputs/kaplan-files.json`: Kaplan's files used (URL, bytes, SHA-256, number of shapes, role). `selected`
  files contain selected shapes; `searched` files were read only to complete the selection (or, for
  `19omino_2up.txt`, as parents of the restricted search).
- `bridge/file-comparison.jsonl.gz`: one row per checked CNF: `name` (as in §3), grid, K, mode, `status`
  (`CNF_MULTISET_ISOMORPHIC`), `producer_sha256`/`producer_bytes` (the checked file, equal to `cnf` in §3),
  SHA-256 of the transcription of the Lean `cnfOrd` with the default and with the recovered counter order,
  SHA-256 of the variable bijection, variables and clauses.
- `counts/table.json`: one row per shape–variant combination (Table 6), with both implementations' prefix
  counts, totals and inner-enumeration exhaustion proofs (CNF and proof hashes, drat-trim result).
  `counts/inner-parts/<case>.json.gz`: `first` and `second`, the inner parts (layers `≤ k−1`) recorded by each
  implementation as lists of `[layer, cells]`, each with its number of outer completions (`outer`); the second
  implementation also gives one completed k-corona per inner part. A `null` count of the first implementation
  means not computed (15-hex #315).
- `search/`: `candidates.jsonl.gz` (id = SHA-256 of the canonical form, cells, construction family, parents),
  `classification.jsonl` (`K1_UNSAT`, `K3_UNSAT` or `periodic_tiler`), `periodic-tilings.jsonl.gz` (lattice
  `(a,0),(b,d)` with `index = a·d` cells per fundamental domain and the copies in it), `sat-patches.jsonl.gz`
  (saved satisfying patches as witnesses), `summary.json`, `solver-crosscheck.json`, `sample-certificates.json`.
