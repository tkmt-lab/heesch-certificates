# Entry point for a computational reader

Start with README.md, claims.json and VERIFICATION-RECORD.md. The article is paper-heesch-certificates-v2.1-en.tex.

Keep the kinds of evidence apart (claims.json, `kind`):
- `lean-proof`: the soundness of the SAT encoding (six theorems `Heesch.hh_sound_*`, `Heesch.hc_sound_*` for the square, hexagonal and triangular grids, and `HeeschProof.cnfOrd_square`). They say: if the CNF `cnfOrd G ord S K blocks` is unsatisfiable, there is no K-layer corona. They do not say that any particular DIMACS file is unsatisfiable or equals `cnfOrd`.
- `finite-computation`: witnesses (two geometric checkers), drat-trim acceptance of 5,019 proofs, the recorded file comparison between the checked DIMACS files and `cnfOrd`, the counting comparison, the search records. These programs are not formally verified.
- `independent-implementation`: a second encoding agreeing on values; two counting implementations agreeing on counts (they share the CNF generator, hole clauses, grid definitions and checker).
- `prose`: Lemma 1, Proposition 6, the disc criteria used in counting, the stronger empty-block consequence.

Do not describe the values as proved in Lean, the counts as certified, the search as exhaustive, or the work as human-reviewed. Do not extend the claims beyond the 3,964 listed shapes or to placements off the grid.

Commands (no network needed except fetch_inputs.py and tools/build_drat_trim.sh):
- `python3 -B check_packet.py` (seconds): inventory, claims, record cross-checks, privacy.
- `python3 -B ci_check.py` (about 4 minutes, needs python-sat and drat-trim): what the CI runs.
- `python3 -B recheck_certificates.py --all` (hours): every upper bound.
- Lean: formal/README.md.

Names: `omino`, `hex`, `iamond` are the square, hexagonal and triangular grids. Shape identifiers such as "15-hex #315" are zero-based indices in Kaplan's file (here 15hex_3up.txt, index 315). In counts/, "first" and "second" are the two counting implementations of Section 9.
