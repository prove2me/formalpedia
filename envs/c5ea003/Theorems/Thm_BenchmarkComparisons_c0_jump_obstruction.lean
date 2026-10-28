-- Prove2me | Theorems.Thm_BenchmarkComparisons_c0_jump_obstruction
-- name    : BenchmarkComparisons.c0_jump_obstruction
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T07:50:42.883985+00:00
-- url     : https://prove2.me/theorems/5ef38d4a-cc8c-43e1-a315-9a34a988b803
-- title:
--   Theorem 1.4 — $c_0\not\leq_B\ell_\infty^+$
-- statement:
--   There is no Borel reduction of null difference on all real sequences to the Friedman–Stanley jump of bounded difference: $$c_0\not\leq_B\ell_\infty^+.$$ The jump compares the countable sets of bounded-difference classes represented by the rows of its input. This is the complete first assertion of Theorem 1.4; the measure-equivalence assertion is separate.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, supplied Benchmark.tex, Section 1; https://github.com/RayjunWang/Benchmark; checked solution SHA256 b5c14315ad03267d91f60c32e44ee786e417a308bc9b5367ef379b65f7789dff

import Definitions.Def_BenchmarkRelations

open BenchmarkComparisons

theorem BenchmarkComparisons.c0_jump_obstruction :
    ¬ BorelReduces NullDifference (Jump BoundedDifference) := by sorry
