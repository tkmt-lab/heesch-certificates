# Heesch numbers of small polyforms with certificates and a Lean-verified SAT encoding

Release 1.0.0 of https://github.com/tkmt-lab/heesch-certificates (tag `v1.0.0`). The article is
[paper-heesch-certificates-v2.1-en.pdf](paper-heesch-certificates-v2.1-en.pdf) (version 2.1, 15 pages).

## In brief

A shape that does not tile the plane can sometimes still be surrounded by layers (coronas) of copies of
itself. Its Heesch number is how many complete layers fit. Craig S. Kaplan computed these numbers with a
SAT solver for thousands of small polyominoes, polyhexes and polyiamonds, in two variants: Hc (no holes
anywhere) and Hh (holes allowed in the outermost layer). This packet attaches checkable evidence to a fixed
selection of 3,964 of his shapes: a concrete corona for every lower bound, a proof of unsatisfiability for
every upper bound, and a Lean proof that the SAT encoding is sound, i.e. that an unsatisfiable formula
really rules out the corona. It also counts the maximal coronas of 22 shapes and records a restricted search
for a polyomino with Heesch number 4.

## What is claimed

1. **Values.** For each of the 3,964 shapes listed in Table 3 of the article (all non-tilers of Kaplan's
   files with 7–10 square cells, 6–8 hexagons and 7–12 triangles, plus the five polyominoes with Hh = 3, the
   fifteen polyhexes with 9–16 cells and Hh = 4, and the two polyiamonds with Hh = 4 in his threshold files),
   the pair (Hc, Hh) equals Kaplan's: 6,574 corona witnesses give the lower bounds, and 5,019 CNF formulas,
   each accepted as unsatisfiable by drat-trim, give the upper bounds.
2. **Soundness (Lean).** On the square, hexagonal and triangular grids, for every finite S, every K ≥ 1,
   every order of the at-most-one counter inputs and every list of valid hole blocks: if the CNF
   `cnfOrd G ord S K blocks` is unsatisfiable, S has no K-layer Hh-corona (respectively Hc-corona). Six
   theorems `Heesch.hh_sound_{square,hex,tri}`, `Heesch.hc_sound_{square,hex,tri}`; axioms `propext`,
   `Classical.choice`, `Quot.sound` only; accepted in six kernel runs using five implementations (Comparator).
3. **File correspondence.** Each of the 5,019 checked DIMACS files is, up to renaming of variables and
   reordering of clauses and literals, the Lean `cnfOrd` for the recorded shape, K, blocks and the counter
   order recovered from the file (a recorded finite comparison).
4. **Second encoding.** A separately written encoding agrees on every value (no proof logs).
5. **Maximal coronas.** Table 6 of the article: prefix counts and totals for 30 shape–variant combinations,
   with two separate counting implementations agreeing completely on 28 of them.
6. **Restricted search.** None of the 3,442 polyominoes with 20–28 cells of a fixed, non-exhaustive
   collection has a finite Hh = 4.

[claims.json](claims.json) lists each claim with its kind of evidence (`lean-proof`, `finite-computation`,
`independent-implementation`, `prose`), the files behind it and how to re-check it.

## Scope and what is not claimed

- Only the listed shapes. Polyominoes with 11–19 cells and Hh ≤ 2, polyhexes with 9–16 cells and Hh ≤ 3,
  polyhexes with 17 or more cells and polyiamonds with 13–24 cells and Hh ≤ 3 are outside the selection.
  That Kaplan's files contain every non-tiler of each size is taken from his enumeration.
- Copies on the fixed grid only (as in Kaplan's SAT setting).
- drat-trim is not formally verified; there is no LRAT or verified-checker run, and no proof inside Lean that
  the files equal `cnfOrd`. The end-to-end statement rests on the Lean kernel and Mathlib, the faithfulness of
  the Lean definitions (read by an independent AI reader: "faithful with caveats"), drat-trim, SHA-256 and the
  file-comparison programs, and for lower bounds the geometric checkers.
- The outer-layer counts of Section 9 have no proof certificate; for 15-hex #315 the totals come from one
  implementation only. The search of Section 10 does not show that no polyomino has Hh = 4.
- No human expert review has taken place. No priority is claimed.

## Check in a minute

Python 3.11 with the packages of [requirements.txt](requirements.txt) (`python3 -m pip install -r requirements.txt`).
From the repository root:

```sh
python3 -B check_packet.py              # file list, hashes, claims, records cross-checked, privacy (seconds)
python3 -B checkers/check_all_witnesses.py   # both geometric checkers on all 6,574 witnesses (~10 s)
```

The second command ends with a line like

```text
{"status": "PASS", "shapes": 3964, "witnesses_first_checker": 6574, "witnesses_second_checker": 6574, ...}
```

To re-check one upper bound end to end (regenerate the CNF, compare its SHA-256, solve it with the recorded
solver, check the proof with drat-trim; a few seconds):

```sh
sh tools/build_drat_trim.sh                  # clones drat-trim at the pinned commit and compiles it
python3 -B recheck_certificates.py --name omino_10omino_0up_0000_0
```

## More checks

- `python3 -B ci_check.py` runs what the CI runs (about 4 minutes on a laptop): both witness checkers, `check_counts.py`
  (both counting implementations recompared in cell coordinates; every inner part and completed corona
  checked geometrically), `check_search.py` (candidate identities, all 576 periodic tilings, all 513
  satisfying patches), Figure 1 regenerated and compared with the article source, and
  `recheck_certificates.py --sample` (a stratified sample of the certificates, all three grids, Hh and Hc
  with hole blocks, all three solvers).
- `python3 -B recheck_certificates.py --all` re-checks all 5,019 certificates (about 3–4 hours on one core;
  peak memory about 3 GB for the largest proof of 7.2 GB; at least 10 GB of free disk). `--cnf-only` only
  regenerates the CNFs and compares their hashes.
- Kaplan's files are not included (see below). `python3 -B fetch_inputs.py --directory DIR` downloads them
  from the original site and verifies the hashes; `python3 -B checkers/check_all_witnesses.py --inputs DIR`
  then compares every shape and value with them.
- Lean: see [formal/README.md](formal/README.md). With elan installed, from `formal/`:
  `lake exe cache get && lake build && lake env lean ../ci/Axioms.lean`, and
  `lake comparator --config comparator.json --paranoid` (Linux with bubblewrap).

The file comparison of Section 7 is shipped as per-CNF records (`bridge/`), not as programs: the transcriptions
of `cnfOrd`, the counter-order recovery and the multiset comparison were research scripts tied to local input
archives and would need rewriting to run elsewhere. Each record gives the SHA-256 of the checked file, of the
transcription with the default and the recovered counter order, and of the variable bijection.

The search program is `search/search.py`: `python3 -B search/search.py generate --inputs DIR` (DIR from
`fetch_inputs.py`) rebuilds the candidate list in `$SEARCH_OUTPUT` (default `./search-output`) in about 10 seconds,
with the SHA-256 recorded in `check_search.py`; its `search` step re-runs the SAT screening (hours).

The CNFs (8.7 GB in total) and proofs (25.2 GB) are not stored: the CNFs regenerate byte for byte, and any
proof accepted by drat-trim certifies unsatisfiability. Their recorded SHA-256 are in `certificates/`.

## Files

| Path | Content |
|---|---|
| `paper-heesch-certificates-v2.1-en.{tex,pdf}` | the article; `figures/make_figure1.py` regenerates Figure 1 |
| `FORMAT.md` | definitions, the encoding, and every record format |
| `formal/`, `ci/Axioms.lean`, `evidence/` | Lean statement and proof, Comparator configuration and recorded output |
| `witnesses/`, `checkers/` | lower-bound witnesses and the two geometric checkers |
| `certificates/`, `generator/`, `recheck_certificates.py`, `tools/` | upper-bound records, the CNF generator, the re-check |
| `bridge/` | per-CNF records of the comparison with the Lean `cnfOrd` |
| `counts/`, `check_counts.py` | maximal-corona counts of both implementations |
| `search/`, `check_search.py` | the restricted search: records and the search program |
| `inputs/`, `fetch_inputs.py` | Kaplan's files: URLs, sizes, SHA-256 |
| `claims.json`, `VERIFICATION-RECORD.md`, `PROVENANCE.json`, `source-derivatives.json`, `SHA256SUMS` | records |

## Data from Kaplan's dataset

The shapes and reference values come from Kaplan's dataset (https://cs.uwaterloo.ca/~csk/heesch/), whose
page states no licence. The dataset files are therefore not redistributed here; `inputs/kaplan-files.json`
identifies them by URL and SHA-256. The witness and certificate records contain the cell coordinates of each
selected shape, because every check needs them.

## Research and verification

The author is Tatsuhiko Takimoto, Independent researcher. AI systems assisted with the computation of the
values, witnesses and proofs, the second encoding and the geometric checkers, the Lean statement and proof,
the independent reading of the Lean statement, the file comparison, the maximal-corona enumeration and
counting, the search, literature organization and drafting; the author is responsible for the claims and
their stated scope. Who checked what, when and with which tools is in
[VERIFICATION-RECORD.md](VERIFICATION-RECORD.md).

## Built on prior work

- Craig S. Kaplan's study of the Heesch numbers of unmarked polyforms ([Contrib. Discrete Math. 17(2), 2022](https://doi.org/10.55016/ojs/cdm.v17i2.72886)),
  its dataset and the heesch-sat software: the question, the definitions of coronas, Hc and Hh, the SAT
  formulation over all layers, the shapes and every reference value come from this work.
- The Heesch challenge of Layr-Labs/Eigen and its contributors, which first attached checkable certificates
  (witness checks, CNF digests, LRAT checked by cake_lpr) to Heesch numbers.
- Heinrich Heesch's problem; Casey Mann's survey; Casey Mann and Bruce Thomas's computations for edge-marked
  polyforms; Bojan Bašić's figures with Heesch number 6.
- Marijn Heule, Nathan Wetzler and Warren Hunt's drat-trim; Armin Biere's CaDiCaL and Lingeling; Gilles
  Audemard and Laurent Simon's Glucose; Alexey Ignatiev, Antonio Morgado and Joao Marques-Silva's PySAT;
  Carsten Sinz's sequential counter.
- Lean 4 and Mathlib, Comparator and the external kernels lean4lean, nanoda, con-leche and con-ron; the
  verified-encoding work of Cayden Codel, Jeremy Avigad and Marijn Heule, and the empty-hexagon verification
  of Bernardo Subercaseaux and colleagues, which this formalization follows in approach.

I am grateful to them, and I hope this work adds something new to the field they opened. These
acknowledgements imply no endorsement.

Code: Apache-2.0. Article, original text and generated data: CC BY 4.0. See [LICENSE](LICENSE).
Contact: GitHub Issues at the repository.
