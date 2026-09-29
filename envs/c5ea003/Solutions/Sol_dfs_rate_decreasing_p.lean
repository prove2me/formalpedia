-- Prove2me | solution 1 for dfs_rate_decreasing_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:09:48.877195+00:00
-- url     : https://prove2.me/submissions/1df11c05-dc8c-4791-aa27-a2bcece067ca

-- Sol generated from MachineLearning/Neural/QuantumNeuralArchitecture.lean
import Mathlib

/-! # CatalogBuild.Physics.Quantum.QuantumNeuralArchitecture

Auto-generated from theorem catalog database.
Domain: Physics/Quantum
Declarations: 15
-/

noncomputable section

















theorem solution(n : ℕ) (hn : 1 ≤ n) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : 1 ≤ k
    · have := ih hk
      have h1 := Nat.one_le_pow k 2 (by omega)
      calc k + 1 + 1 ≤ 2 ^ k + 1 := by omega
        _ ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ k * 2 := by ring
        _ = 2 ^ (k + 1) := (pow_succ 2 k).symm
    · interval_cases k; norm_num
