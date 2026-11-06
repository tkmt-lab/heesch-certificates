# Changelog

## 1.0.1 (2026-11-09)

- Enable the required libc declarations when building the pinned drat-trim source with a strict C99 compiler,
  fixing the GCC 14 build failure.
- Require both `s VERIFIED` and exit status zero from drat-trim; add failure controls for abnormal exits,
  missing success output and timeouts. Use Bash pipefail for the Lean CI gates so a failing command
  cannot be hidden by its output pipeline.
- Document Poppler, compiler and Git requirements, distinguish fresh computation from comparisons of stored
  records, and align the local check instructions with the separate records and Lean CI jobs.
- Correct the input-file breakdown to 22 files with selected shapes and 19 other searched files (including
  the restricted-search parent file).
- Mathematical claims are unchanged. Article version 2.1, the Lean statements and proofs, and the numerical
  data are unchanged.

## 1.0.0 (2026-10-23)

- First release: article version 2.1 (15 pages); Lean statement and proof of the encoding soundness on three grids;
  6,574 witnesses and two checkers; 5,019 certificate records with the CNF generator and a re-check script;
  per-CNF file-comparison records; maximal-corona count records of two implementations; restricted-search records.
