-- Prove2me | Theorems.Thm_BenchmarkComparisons_all_main_comparisons
-- name    : BenchmarkComparisons.all_main_comparisons
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T06:56:55.85643+00:00
-- url     : https://prove2.me/theorems/e51f68cc-69f7-4eb6-b875-8a89d44eff6d
-- title:
--   All six introductory benchmark comparisons
-- statement:
--   The conjunction of Theorems 1.1–1.6: $E_\infty^\omega\leq_B c_0$ and $E_\infty\perp_B\ell_p$ for all finite $p\geq1$; the threshold $\ell_p\leq_B\equiv_m$ exactly for $p\leq2$, including $p=\infty$; $c_0\not\leq_B\equiv_m$; both nonreductions to $\ell_\infty^+$; strict measure-to-operator reducibility; and the full chain involving arbitrary representations of $\mathbb Z$ and $F_\infty$. All relations, Borel structures and quantifiers are those fixed by the shared definitions.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, supplied Benchmark.tex, Section 1; source SHA256 c3c80147a17922e19044935df97b27a2a2a0be5f86665e0869d6a376250d6330; repository designated by the author: https://github.com/RayjunWang/Benchmark. Theorems 1.1–1.6. This is a conjunction of the six exact assertions, with no additional hypotheses.

import Definitions.Def_BenchmarkRelations

open BenchmarkComparisons

theorem BenchmarkComparisons.all_main_comparisons :
    CountableComparisons ∧ ExponentThreshold ∧ NullMeasureObstruction ∧
    JumpObstructions ∧ OperatorStrictComparison ∧ RepresentationComparisons := by sorry
