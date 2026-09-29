-- Prove2me | solution 1 for local_cost_advantage_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:11:32.46446+00:00
-- url     : https://prove2.me/submissions/11a1d8d0-57bf-4598-8f71-528e0ce81b5b

-- Sol generated from MachineLearning/Neural/QuantumNeuralArchitecture.lean
import Mathlib

/-! # CatalogBuild.Physics.Quantum.QuantumNeuralArchitecture

Auto-generated from theorem catalog database.
Domain: Physics/Quantum
Declarations: 15
-/

noncomputable section

















theorem solution(n : ℕ) (hn : 5 ≤ n) : 2 ^ n > n ^ 2 := by
  induction hn with
  | refl => norm_num
  | @step k hk ih =>
    show 2 ^ (k + 1) > (k + 1) ^ 2
    have hk5 : (k : ℤ) ≥ 5 := by exact_mod_cast hk
    have h2 : 2 * k ^ 2 ≥ (k + 1) ^ 2 := by
      have : (2 : ℤ) * (k : ℤ) ^ 2 ≥ ((k : ℤ) + 1) ^ 2 := by nlinarith [sq_nonneg ((k : ℤ) - 1)]
      exact_mod_cast this
    calc (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      _ ≥ (k ^ 2 + 1) * 2 := by omega
      _ = 2 * k ^ 2 + 2 := by ring
      _ > 2 * k ^ 2 := by omega
      _ ≥ (k + 1) ^ 2 := h2
