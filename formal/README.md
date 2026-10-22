# Lean formalization of the encoding soundness

Lean 4.35.0, Mathlib v4.35.0 (`lean-toolchain`, `lake-manifest.json`). The statement imports only Mathlib.

| Module | Content |
|---|---|
| `Heesch/Challenge.lean` | **the statement**: grids, coronas, holes, discs, the pruning `candidates`, the CNF `cnfOrd`, `HoleBlock.Valid`, and the six theorems with `sorry`. Written before the proof. |
| `Heesch/Spec.lean` | the definitions of `Challenge.lean` (namespace `Heesch` up to `cnf`), copied character for character so that proofs can import them |
| `Heesch/Solution.lean` | the rest of the statement's namespace with the six proofs filled in |
| `Heesch/Basic.lean`, `Cand.lean`, `Ord.lean`, `Main.lean`, `Inst.lean` | the proof: grid-generic lemmas, survival of genuine copies under pruning, the assignment from a corona, the clauses, the grid facts for the three grids |
| `Heesch/SquareEq.lean` + `Heesch/Square/*.lean` | `HeeschProof.cnfOrd_square`: `cnfOrd squareGrid` equals the earlier square-only definition `HeeschSquareProof.cnfOrd` (used by the file comparison of the 2,076 square CNFs); outside the Comparator statement |

The six theorems are `Heesch.hh_sound_square`, `Heesch.hc_sound_square`, `Heesch.hh_sound_hex`,
`Heesch.hc_sound_hex`, `Heesch.hh_sound_tri`, `Heesch.hc_sound_tri`.

## Build and check

```sh
lake exe cache get                       # prebuilt Mathlib
lake build                               # Heesch.Solution and Heesch.SquareEq (about 2 minutes, < 2.1 GB per file)
lake build Heesch.Challenge              # the statement (six sorry warnings expected)
lake env lean ../ci/Axioms.lean          # every line: [propext, Classical.choice, Quot.sound]
lake comparator --config comparator.json --paranoid   # Linux with bubblewrap
```

`Heesch.Challenge` and `Heesch.Solution` declare the same names and are not imported together; the default
target `Heesch` imports only the proof side. `comparator.json` permits the axioms `propext`, `Quot.sound`,
`Classical.choice`. With `--paranoid`, Comparator replays the solution in the Lean kernel (paranoid and default
mode) and in lean4lean, nanoda, con-leche and con-ron.

## Names

The files were written in a research workspace under other module and namespace names. For publication they
were renamed with an identifier map and nothing else in the Lean code was changed (comments were edited to
remove internal labels; `source-derivatives.json` lists the original and public SHA-256 of every file):

| Original | Public |
|---|---|
| namespace of the statement (three grids) | `Heesch` |
| namespace of the proof (three grids) | `HeeschProof` |
| namespace of the earlier square-only statement | `HeeschSquare` |
| namespace of the earlier square-only proof | `HeeschSquareProof` |
| modules | `Heesch.<Name>`, `Heesch.Square.<Name>` as in the table above |

Comments mention the earlier square-only modules `Heesch.Square.Challenge`, `Heesch.Square.Solution`,
`Heesch.Square.Assign`, `Heesch.Square.Clauses`, `Heesch.Square.Amo`, `Heesch.Square.Hole` and
`Heesch.Square.Main`. They contain the first, square-only proof, which the three-grid proof generalizes; they are
not needed for any theorem here and are not included. Section numbers in comments (§1, §1.1, §3, §4.x) refer to
`../FORMAT.md`.

## Records

- `../evidence/comparator-2026-10-22.txt`: the Comparator run of 22 October 2026 under the original names (the
  identifier map above applied to the log, nothing else): all six kernel runs accept; 42.1 s, 1.91 GB. It was run
  on macOS without the bubblewrap sandbox (`--inadvisably-no-sandbox`).
- `../evidence/comparator-public-names-2026-10-23.txt`: the same check on the renamed files of this packet.
- The CI job `lean` repeats the build, the axiom check and Comparator with the sandbox on Linux.
