-- Prove2me | solution 1 for GarsiaQBinom.qFactorial_product
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:21:39.767584+00:00
-- url     : https://prove2.me/submissions/293fb864-acc2-4b00-8d98-ea4ce08ba713

import Mathlib
import Definitions.Def_Speculative_NumberTheory_GarsiaQBinomial
open GarsiaQBinom Polynomial in
theorem solution : ∀ {n k : ℕ}, k ≤ n →
    qBinom n k * qFactorial k * qFactorial (n - k) = qFactorial n := by
  -- q-binomials vanish above the diagonal
  have hzero : ∀ n k, n < k → qBinom n k = 0 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rfl
    | succ n ih =>
      intro k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [qBinom, ih k' (by omega), ih (k' + 1) (by omega)]
      ring
  -- `[a + b]_q = [a]_q + q^a [b]_q`
  have hqnat : ∀ a b : ℕ, qNat (a + b) = qNat a + X ^ a * qNat b := by
    intro a b
    unfold qNat
    rw [Finset.sum_range_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    simp [qBinom, qFactorial]
  | succ n ih =>
    intro k hk
    cases k with
    | zero => simp [qBinom, qFactorial]
    | succ k =>
      rw [qBinom, show n + 1 - (k + 1) = n - k by omega]
      rcases Nat.lt_or_ge k n with hkn | hkn
      · -- q-Pascal step, using the induction hypothesis at `k` and `k + 1`
        have h1 := ih (k := k) (by omega)
        have h2 := ih (k := k + 1) (by omega)
        obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
        rw [show n - (k + 1) = j by omega] at h2
        rw [hj] at h1 ⊢
        simp only [qFactorial] at h1 h2 ⊢
        calc (qBinom n k + X ^ (k + 1) * qBinom n (k + 1)) * (qFactorial k * qNat (k + 1))
              * (qFactorial j * qNat (j + 1))
            = (qBinom n k * qFactorial k * (qFactorial j * qNat (j + 1))) * qNat (k + 1)
              + X ^ (k + 1) * (qBinom n (k + 1) * (qFactorial k * qNat (k + 1)) * qFactorial j)
                * qNat (j + 1) := by ring
          _ = qFactorial n * qNat (k + 1) + X ^ (k + 1) * qFactorial n * qNat (j + 1) := by
              rw [h1, h2]
          _ = qFactorial n * qNat (n + 1) := by
              rw [show n + 1 = (k + 1) + (j + 1) by omega, hqnat (k + 1) (j + 1)]
              ring
      · -- the diagonal `k = n`
        obtain rfl : k = n := by omega
        rw [hzero k (k + 1) (by omega), Nat.sub_self]
        have h1 := ih (k := k) le_rfl
        rw [Nat.sub_self] at h1
        simp only [qFactorial] at h1 ⊢
        linear_combination qNat (k + 1) * h1
