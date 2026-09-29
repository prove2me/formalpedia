-- Prove2me | solution 1 for mme_CW_repeated_power_rate_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:31.555454+00:00
-- url     : https://prove2.me/submissions/9b6a913b-eae9-493a-85be-ebb56a6c72f7

import Theorems.Thm_mme_CW_repeated_power_matrix_weight_upper

open MME BigOperators
universe u
set_option autoImplicit false

/-- A matrix extraction whose normalized rate exceeds the CW rank rate forces
an upper bound on the matrix multiplication exponent. -/
theorem solution
    {K : Type u} [Field K] (q N inputs copies : ℕ)
    (hinputs : 0 < inputs) (a b c : Fin copies → ℕ)
    (tau rate : ℝ) (htau : 0 < tau)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (TensorObj.bigAdd (fun _ : Fin inputs => (CWObj K q).kronPow N)))
    (hweight : (inputs : ℝ) * Real.exp rate ≤
      ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau)
    (hsurplus : (N : ℝ) * Real.log (q + 2 : ℕ) < rate) :
    matMulExp_strassen K < 3 * tau := by
  by_contra hnot
  have htau_le : tau ≤ matMulExp_strassen K / 3 := by linarith
  have homega : 0 < matMulExp_strassen K / 3 := by
    have := matMulExp_strassen_pos (K := K)
    positivity
  have hmono : (∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) ≤
      ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hz : a j * b j * c j = 0
    · simp only [hz, Nat.cast_zero, Real.zero_rpow htau.ne', Real.zero_rpow homega.ne', le_refl]
    · apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      · exact htau_le
  have hupper := mme_CW_repeated_power_matrix_weight_upper q N inputs copies a b c hrestrict
  have hexp : Real.exp rate ≤ ((q + 2 : ℕ) : ℝ) ^ N := by
    have hin : 0 < (inputs : ℝ) := by exact_mod_cast hinputs
    have hbound := hweight.trans (hmono.trans hupper)
    nlinarith
  have hbase : 0 < ((q + 2 : ℕ) : ℝ) := by positivity
  have hstrict : ((q + 2 : ℕ) : ℝ) ^ N < Real.exp rate := by
    calc
      _ = Real.exp ((N : ℝ) * Real.log (q + 2 : ℕ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hbase]
      _ < Real.exp rate := Real.exp_lt_exp.mpr hsurplus
  exact (not_lt_of_ge hexp) hstrict


#print axioms solution
