# Verification record: heesch-certificates 1.0.0

This record carries the process and provenance details kept out of the article (version 2.1, referenced once
from its Section 2). The article states the mathematics and the present scope; this file states who checked
what and when, which computations are independent of which, which AI readings took place, and what the packet
checks. Dates are 2026, times JST (UTC+9) unless marked UTC. All work was done by the author with AI systems
in separate sessions ("sessions" below); no human expert review has taken place. The packet was assembled and
checked as a local release candidate; publication is a separate step taken by the author.

## 1. Inputs

- Kaplan's dataset (https://cs.uwaterloo.ca/~csk/heesch/), retrieved with curl on 20 October (polyominoes) and
  20–22 October (polyhexes, polyiamonds). No licence is stated on the page, so the files are not redistributed;
  `inputs/kaplan-files.json` records URL, bytes and SHA-256 of all 41 files used (28 with selected shapes,
  13 searched only to complete the selection or, for `19omino_2up.txt`, as parents of the restricted search).
- The 17-hex file returned HTTP 403, so polyhexes with 17 or more cells are outside the selection. Kaplan's
  census has no non-tiling 8-iamonds (his Table 5), so there is no 8-iamond file.
- The selection (Table 3 of the article) was fixed on 21 October: all polyominoes up to 10 cells, the
  polyominoes with H >= 3, and the polyhex and polyiamond files that had been run by then.

## 2. Main computation: values, witnesses, proofs (20–21 October)

- One session computed (Hc, Hh) for 3,964 shapes with the generator in `generator/` (python-sat 1.9.dev17:
  CaDiCaL 1.5.3, Glucose 4.1, Lingeling) and drat-trim at commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`
  (24 November 2024, MIT licence), each run under a 1 GB memory cap and 30-minute limit. All pairs agree with
  Kaplan's. The encoding and file formats were written down first in a specification (`FORMAT.md` is its
  English version, with the same section numbers).
- 6,574 witnesses passed `checkers/check_witness.py`. Of the 5,019 certificates, 5,015 were accepted by
  drat-trim within 1 GB; four five-layer Hh bounds (13-hex #19, 15-hex #278, 15-hex #315, 20-iamond #130)
  needed more memory. They were regenerated and checked on 21 October under a 6 GB cap and again on
  22 October under a 4.5 GB cap: CNF and proof SHA-256 equal to the records, all `s VERIFIED`, peak resident
  memory 3,011,756,032 bytes (15-hex #315), 2,663 s for the four. The certificate records note the cap
  (`drat_trim.memory_cap_mb`).
- Solver and proof formats: CaDiCaL binary DRAT 4,998, Glucose DRUP 16, Lingeling text DRAT 5. Largest proof:
  15-hex #315, 7,175,887,914 bytes. Total sizes: CNFs 8,701,205,806 bytes, proofs 25,184,139,473 bytes; neither
  is archived (Section 7 below).
- Recorded deviations from the run rules: one measurement under a 1.4 GB cap (peak 847 MB); a temporary 7.2 GB
  proof file exceeded the 5 GB disk rule and was deleted after checking.

## 3. Second encoding and second witness checker (21 October)

- A separate session wrote a second CNF encoding and the second geometric checker (`checkers/geometry.py`,
  Python standard library only) from the specification alone, without reading the generator code.
- Results: all 3,964 shapes and 6,574 witnesses pass geometrically and against Kaplan's files; every witness,
  read as an assignment, satisfies the second encoding's clauses; all 5,019 upper-bound instances are
  unsatisfiable there (the last one, 15-hex #315 Hh K=5, with Glucose 4 in 259 s after a 4-hour CaDiCaL budget
  ended undecided); (Hc, Hh) agree for all shapes. This computation kept no proof logs; it corroborates the
  values and is not a second certificate. It shares the specification and the SAT solvers with the first.

## 4. Lean statement, reading, proof, Comparator (21–22 October)

Environment: Lean 4.35.0, Mathlib v4.35.0. One Lean process at a time.

- Square grid first (21–22 October): a statement written before the proof, an independent AI reading
  ("faithful with caveats"), a proof, and a Comparator check (six kernel runs, five implementations, 5,501
  declarations). This square-only development is superseded by the three-grid one; only the part needed for
  `cnfOrd_square` is included (`formal/Heesch/Square/`).
- Three grids (22 October): plan 10:21–10:31; statement `Heesch/Challenge.lean` written 10:31–10:33 before any
  proof; proof 10:35–10:45; Comparator 10:45–10:46; `cnfOrd_square` 10:48–10:50. The statement and the proof
  were written by the same session.
- Reading of the statement: a fresh session of a different AI system, 10:33–10:43, given only the statement,
  the specification and a list of questions. Verdict "faithful with caveats" (14 findings, no change required).
  It checked cells, neighbours, orientations and translation classes on both new grids, compared both distance
  formulas with breadth-first search, checked the triangular pinch test on all 64 occupancy patterns around a
  vertex, and confirmed on small examples that the definitions are not vacuous. The proof was started before
  the reading finished; the statement was not changed after 10:33 (the read file and the proved file have the
  same SHA-256). The caveats are part of the scope (README, claims.json).
- Comparator (`lake comparator --paranoid`, on macOS without the bubblewrap sandbox): Lean kernel in paranoid
  and default mode, lean4lean, nanoda, con-leche (5,674 declarations), con-ron (5,674) all accept; 42.1 s,
  1.91 GB. The coordinating session re-ran it and saw the same acceptance. `#print axioms`:
  `propext`, `Classical.choice`, `Quot.sound` for all six; no `sorry`, `native_decide` or new axiom. The
  recorded output is `evidence/comparator-2026-10-22.txt` (with the public module and namespace names
  substituted, nothing else changed).
- Renaming for publication (23 October): modules and namespaces were renamed and comments edited to remove
  internal labels (`formal/README.md`, `source-derivatives.json`). The renamed files were built module by module
  (14 modules, about 80 s, at most 2.03 GB per Lean process), `ci/Axioms.lean` printed the three standard axioms
  for the six theorems and `HeeschProof.cnfOrd_square`, and Comparator was run again on the renamed files on
  23 October 01:32 (29.7 s, 1.91 GB, again without sandbox on macOS): all six kernel runs accept
  (`evidence/comparator-public-names-2026-10-23.txt`).

## 5. File comparison: checked CNFs and the Lean `cnfOrd` (21–22 October)

- Performed by the session that wrote the second encoding, which ran the generator only as a black box (its
  source was identified by hash and not read) and transcribed the Lean definition of `cnfOrd` into Python.
- First attempt on 11 small cases (1–3-ominoes with K = 1, 2 and three 7-ominoes): only 2 matched up to renaming,
  because the generator lists the inputs of the at-most-one counters in a different order from the Lean
  definition. This led to the order-generic theorem (`ord` as an argument). After recovering the order from each
  file, all 11 matched.
- Square grid, all 2,076 CNFs (21 October, 17:43–18:31 UTC): 178,454,670 clauses, 45,711,523 variables; 7,267
  blocks in 460 CNFs valid; 50 cases needed the fresh variable of (F) to be renumbered (generator after the cell
  variables, Lean after the counter variables); 30 byte-for-byte comparisons of the Python transcription with
  Lean's own evaluation of the square-only definition.
- Hexagonal and triangular grids, 537 + 2,406 CNFs (22 October, audit completed 07:54 UTC): 360,239,738 clauses,
  87,702,271 variables; 0 mismatches; 97 fresh-variable renumberings; 34 byte comparisons with Lean's evaluation
  of the grid `cnfOrd`; 6,020 blocks valid; all 6,922 triangular hole points are cells.
- Every regenerated file had the recorded SHA-256 and size. Clauses were compared as multisets of literal
  multisets, read by two different DIMACS parsers, without merging duplicates, simplification or sign flips.
- No further independent review of the comparison; the transcriptions are validated on 64 Lean outputs, not
  proved. The per-CNF records are `bridge/file-comparison.jsonl.gz`. The comparison programs (the two Python
  transcriptions of `cnfOrd`, the order recovery and the multiset comparison) are not in this packet: they were
  research scripts spread over several directories, tied to frozen local input archives and to running the
  generator as a black box, and they would need to be rewritten to run elsewhere. The records give, for every CNF,
  the SHA-256 of the checked file, of the transcription with the default and with the recovered counter order, and
  of the variable bijection, so a reader can compare an own transcription of `cnfOrd` against them.

## 6. Maximal-corona counts (22–23 October)

- The counting conventions (central stabilizer, copies as cell sets, layer labels, no surplus copies,
  extendable prefixes) were written down before counting.
- First implementation: SAT enumeration of inner parts blocking the selected inner placements, then a memoised
  exact-cover count of outer layers. Second implementation: a separate session, working from the same written
  conventions and inputs without reading the first implementation's results, witnesses or code, blocking the
  complete signed inner assignment and counting outer layers with its own candidate generation and disc tests
  (direct on the square grid, Euler characteristic on the hexagonal grid, with boundary conditions on the
  triangular grid). Shared: the CNF generator, hole clauses, grid definitions and the first witness checker.
- Comparison (23 October, 00:30): prefix sets in cell coordinates, all prefix counts, every per-inner-part
  completion count and the totals agree in 28 of 30 combinations; both sides have drat-trim-checked exhaustion
  proofs for those inner enumerations. For 15-hex #315 the prefix sets agree (Hh 10/29/979, Hc 6/14/79) but
  neither side has a checked exhaustion proof; the totals come from the second implementation only. The first
  implementation completed 26 of the 79 Hc inner parts before its time limit: 22 agree; the other four carry
  nonzero "ambiguous hole check" flags, which its own rule declares invalid. It did not finish the Hh outer
  count; three per-inner values from its log agree. These records are in `counts/` and are recompared by
  `check_counts.py`.
- Further checks: nine direct full enumerations by the first implementation, each ending in a drat-trim-checked
  unsatisfiable call; six full-SAT checks and plain-backtracking recounts of 12 inner parts (eight combinations)
  by the second. Public comparison counts (251, 1,449, 793; first implementation only) are in
  `counts/table.json`.

## 7. Restricted search (22 October)

- A separate session built a fixed collection of 3,442 normalized polyominoes with 20–28 cells from five
  construction families (Section 10), screened at K = 3 (with a K = 1 pretest for part), searched explicit
  periodic tilings, and recorded every outcome. Candidate list SHA-256
  `5fb662257aaccbedeb699bfa966ba128b4a41cf9e52704875622ac579b6817ab`.
- A separate audit (no imports from the generator or solver) checked candidate identities and topology and all
  576 periodic tilings; 14 UNSAT cases agree with a second solver on the same encoding; two sampled screening
  instances have drat-trim-accepted proofs; all 513 saved satisfying patches pass the geometric checker.
  `check_search.py` repeats the identity, topology, tiling and patch checks.
- The search program is included as `search/search.py` (paths and the local capping wrapper replaced, the fixed
  salt kept). On 23 October its `generate` step was re-run from the packet with Kaplan's `19omino_2up.txt` from
  the original site and reproduced the candidate list byte for byte (same SHA-256).

## 8. Literature

- Novelty and prior work were checked by a separate literature session (20–22 October): certificates for
  individual Heesch numbers exist (Layr-Labs/Eigen Heesch challenge), so the article does not claim the first
  certificates; the combination of a fixed table range with witnesses, proofs and a second encoding for every
  value, and a Lean soundness theorem on three grids connected to the checked files, was not found. Several
  references were read only as abstracts and are cited only for their stated topic. The session that computed
  the values did not read the Layr-Labs code.
- New bibliographic entries of version 2 were checked on 23 October against primary metadata or official
  project pages (credit, titles, URLs; not the tools' implementations).

## 9. Article versions and AI readings (not human peer review)

- Version 1 (22 October, 10 pages): written from the records above; counts and hashes recomputed read-only.
- First review (22 October), an independent AI reading of version 1: verdict MINOR, 15 findings. Version 2
  (23 October) addressed all of them and added the counts (Section 9) and the search (Section 10).
- Second review (23 October), an independent AI reading of version 2 that recomputed Table 6 and the inner-part
  sets from the saved records: verdict MINOR (text only), findings F1–F10. Version 2.1 (23 October, 15 pages)
  addresses them; no computation was rerun. Version 2.1 has not been reviewed again.
- For this release the version line reads "Version 2.1, 23 October 2026": the word "(draft)" was removed on
  23 October at the author's request; nothing else in the source changed, and only page 1 of the PDF differs.

## 10. This packet (23 October)

- Assembled by `build_packet.py` in the research workspace from the records above. The article source is
  version 2.1 with "(draft)" removed from the version line; the PDF is rebuilt with Tectonic and a fixed
  SOURCE_DATE_EPOCH. Pages 2–15 render byte-identically (80 dpi) to the pages inspected for version 2.1; page 1
  was viewed again.
- Changes from the research originals are listed in `source-derivatives.json` (original and public SHA-256):
  Lean module/namespace names and comments, docstrings and two path lines of the generator (the original called
  drat-trim through a local memory-capping wrapper), compact re-serialization of the records (fields with local
  paths and internal labels dropped; no value changed).
- New computations for the packet: the Lean build, axiom check and Comparator on the renamed files (Section 4);
  `check_packet.py`, the witness checks, `check_counts.py`, `check_search.py`, Figure 1 and a sampled re-check of
  certificates (`ci_check.py`) in a clean Python 3.11 environment, all PASS (timings in the release notes).
