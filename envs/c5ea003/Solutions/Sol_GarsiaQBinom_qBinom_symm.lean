-- Prove2me | solution 1 for GarsiaQBinom.qBinom_symm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:26:54.15533+00:00
-- url     : https://prove2.me/submissions/83839793-dd88-4cf2-8a3d-0df7a70be5da

import Mathlib
import Definitions.Def_Speculative_NumberTheory_GarsiaQBinomial
open GarsiaQBinom Polynomial in
theorem solution : ∀ {n k : ℕ}, k ≤ n → qBinom n k = qBinom n (n - k) := by
  -- the q-factorial formula `[n k]_q [k]_q! [n-k]_q! = [n]_q!`
  have hprod : ∀ {n k : ℕ}, k ≤ n →
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
  -- q-integers and q-factorials are nonzero polynomials (evaluate at `q = 1`)
  have hnat_ne : ∀ m, qNat (m + 1) ≠ 0 := by
    intro m h
    have h1 := congrArg (Polynomial.eval 1) h
    simp [qNat, Polynomial.eval_finsetSum] at h1
    omega
  have hfac_ne : ∀ m, qFactorial m ≠ 0 := by
    intro m
    induction m with
    | zero => simp [qFactorial]
    | succ m ih =>
      rw [qFactorial]
      exact mul_ne_zero ih (hnat_ne m)
  intro n k hk
  have e1 := hprod hk
  have e2 := hprod (Nat.sub_le n k)
  rw [Nat.sub_sub_self hk] at e2
  -- both sides times `[k]_q! [n-k]_q!` equal `[n]_q!`; cancel in the domain `ℤ[q]`
  have hne : qFactorial k * qFactorial (n - k) ≠ 0 := mul_ne_zero (hfac_ne k) (hfac_ne (n - k))
  apply mul_right_cancel₀ hne
  calc qBinom n k * (qFactorial k * qFactorial (n - k)) = qFactorial n := by
        rw [← mul_assoc]
        exact e1
    _ = qBinom n (n - k) * (qFactorial k * qFactorial (n - k)) := by
        rw [← e2]
        ring
