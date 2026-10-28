-- Prove2me | Theorems.Thm_BenchmarkComparisons_countable_product_to_c0
-- name    : BenchmarkComparisons.countable_product_to_c0
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T07:43:53.60653+00:00
-- url     : https://prove2.me/theorems/047db2a5-ed59-41e6-8635-7790b23f554f
-- title:
--   Theorem 1.1 — $E_\infty^\omega\leq_B c_0$
-- statement:
--   The countable product of the actual full binary shift orbit relation of the free group on two generators Borel reduces to null difference on all real sequences: $$E_\infty^\omega\leq_B c_0.$$ The map preserves and reflects equivalence on every pair, including shift points with stabilizers. This is the complete positive component of Theorem 1.1; its finite-exponent nonreductions are separate targets.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, supplied Benchmark.tex, Section 1; https://github.com/RayjunWang/Benchmark; checked solution SHA256 cfd69e707298a107d2486868ccf254aae872f73eb021ba4736eb66b0b9c0c54c

import Definitions.Def_BenchmarkRelations

open BenchmarkComparisons

theorem BenchmarkComparisons.countable_product_to_c0 :
    BorelReduces (ProductRelation EInfinity) NullDifference := by sorry
