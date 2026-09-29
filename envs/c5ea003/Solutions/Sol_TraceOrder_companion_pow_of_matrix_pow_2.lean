-- Prove2me | solution 2 for TraceOrder.companion_pow_of_matrix_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:47:37.806841+00:00
-- url     : https://prove2.me/submissions/cefeeada-e9a7-4e27-89b2-9077405838c0

import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder

open Matrix TraceOrder in
theorem solution {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K} {n : ℕ}
    (hdet : M.det = 1) (hpow : M ^ (n + 1) = 1)
    (hns : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    chebA M.trace (n + 1) = 0 ∧ chebA M.trace n = -1 := by
  -- Cayley–Hamilton for a `2 × 2` matrix of determinant one
  have hCH : M * M = M.trace • M - 1 := by
    have h2 := hdet
    rw [Matrix.det_fin_two] at h2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply] <;>
      first
        | ring1
        | linear_combination (-1 : K) * h2
  -- powers are Chebyshev combinations of `M` and `1`
  have hpowk : ∀ k : ℕ, M ^ (k + 1)
      = chebA M.trace (k + 1) • M - chebA M.trace k • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro k
    induction k with
    | zero => simp [chebA]
    | succ k ih =>
      rw [pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hCH]
      show _ = (M.trace * chebA M.trace (k + 1) - chebA M.trace k) • M
        - chebA M.trace (k + 1) • (1 : Matrix (Fin 2) (Fin 2) K)
      module
  have h1 := hpowk n
  rw [hpow] at h1
  by_cases hA : chebA M.trace (n + 1) = 0
  · refine ⟨hA, ?_⟩
    rw [hA, zero_smul, zero_sub] at h1
    have h00 := congrFun (congrFun h1 0) 0
    rw [Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    linear_combination h00
  · exfalso
    have e := sub_eq_iff_eq_add.1 h1.symm
    apply hns ((1 + chebA M.trace n) / chebA M.trace (n + 1))
    ext i j
    have hij := congrFun (congrFun e i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply] at hij ⊢
    field_simp
    linear_combination hij
