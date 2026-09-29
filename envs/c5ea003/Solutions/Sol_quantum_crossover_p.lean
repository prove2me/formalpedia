-- Prove2me | solution 1 for quantum_crossover_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:13:16.306542+00:00
-- url     : https://prove2.me/submissions/4f3f13e9-d0fb-412c-8f10-3a689394a028

-- Sol generated from MachineLearning/Neural/QuantumNeuralArchitecture.lean
import Mathlib

/-! # CatalogBuild.Physics.Quantum.QuantumNeuralArchitecture

Auto-generated from theorem catalog database.
Domain: Physics/Quantum
Declarations: 15
-/

noncomputable section

















theorem solution(n : ℕ) (hn : 10 ≤ n) : 2 ^ n > n ^ 3 := by
  induction hn with
  | refl => norm_num
  | @step k hk ih =>
    show 2 ^ (k + 1) > (k + 1) ^ 3
    have hk10 : (k : ℤ) ≥ 10 := by exact_mod_cast hk
    have h2 : 2 * k ^ 3 ≥ (k + 1) ^ 3 := by
      have : (2 : ℤ) * (k : ℤ) ^ 3 ≥ ((k : ℤ) + 1) ^ 3 := by
        nlinarith [sq_nonneg ((k : ℤ) - 3), sq_nonneg ((k : ℤ) * ((k : ℤ) - 3))]
      exact_mod_cast this
    calc (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      _ ≥ (k ^ 3 + 1) * 2 := by omega
      _ = 2 * k ^ 3 + 2 := by ring
      _ > 2 * k ^ 3 := by omega
      _ ≥ (k + 1) ^ 3 := h2
