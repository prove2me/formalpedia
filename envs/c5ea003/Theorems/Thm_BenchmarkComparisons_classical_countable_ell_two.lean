-- Prove2me | Theorems.Thm_BenchmarkComparisons_classical_countable_ell_two
-- name    : BenchmarkComparisons.classical_countable_ell_two
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T06:54:44.024487+00:00
-- url     : https://prove2.me/theorems/09868483-001b-40cd-a1ce-bb9729560273
-- title:
--   Thomas Theorem 6.12 — The established $\ell_2$ obstruction
-- statement:
--   $$E_\infty\not\leq_B\ell_2.$$ There is no Borel map from the full free-two-group shift to all real sequences that preserves and reflects shift-orbit equivalence as square-summable difference. This is an established literature input to the finite-exponent comparison.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, supplied Benchmark.tex, Section 1; source SHA256 c3c80147a17922e19044935df97b27a2a2a0be5f86665e0869d6a376250d6330; repository designated by the author: https://github.com/RayjunWang/Benchmark. Simon Thomas, A descriptive view of unitary group representations, JEMS 17 (2015), Theorem 6.12, p. 1779, https://ems.press/content/serial-article-files/32053?nt=1.

import Definitions.Def_BenchmarkRelations

open BenchmarkComparisons

theorem BenchmarkComparisons.classical_countable_ell_two :
    ¬ BorelReduces EInfinity (LpDifference 2) := by sorry
