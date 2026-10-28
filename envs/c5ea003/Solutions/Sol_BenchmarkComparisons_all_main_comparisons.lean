-- Prove2me | solution 1 for BenchmarkComparisons.all_main_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T14:12:25.886242+00:00
-- url     : https://prove2.me/submissions/db0e6f5a-c9a3-41ac-aee4-70e329a7df2e

import Theorems.Thm_BenchmarkComparisons_theorem_1_1
import Theorems.Thm_BenchmarkComparisons_theorem_1_2
import Theorems.Thm_MeasureEquivalenceMission_c0_not_reducible
import Theorems.Thm_BenchmarkComparisons_theorem_1_4
import Theorems.Thm_BenchmarkComparisons_theorem_1_5
import Theorems.Thm_BenchmarkComparisons_theorem_1_6

theorem solution :
    BenchmarkComparisons.CountableComparisons ∧ BenchmarkComparisons.ExponentThreshold ∧
      BenchmarkComparisons.NullMeasureObstruction ∧ BenchmarkComparisons.JumpObstructions ∧
      BenchmarkComparisons.OperatorStrictComparison ∧ BenchmarkComparisons.RepresentationComparisons :=
  ⟨BenchmarkComparisons.theorem_1_1, BenchmarkComparisons.theorem_1_2,
    MeasureEquivalenceMission.c0_not_reducible, BenchmarkComparisons.theorem_1_4,
    BenchmarkComparisons.theorem_1_5, BenchmarkComparisons.theorem_1_6⟩

#print axioms solution
