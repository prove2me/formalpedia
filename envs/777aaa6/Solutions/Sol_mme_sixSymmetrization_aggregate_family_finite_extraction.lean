-- Prove2me | solution 1 for mme_sixSymmetrization_aggregate_family_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T02:19:06.54612+00:00
-- url     : https://prove2.me/submissions/2617ec59-c3e9-4f22-8f5e-10c03309d93c

import Theorems.Thm_mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

open MME
universe u
set_option autoImplicit false

/-- Keeping a block of volume `H * v` pays the quadratic multiplicity cost
once the exponent is at least two thirds. -/
theorem mme_aggregate_matrix_volume_weight
    (H v : ℕ) (hH : 1 ≤ H) (tau : ℝ) (htau : (2 : ℝ) / 3 ≤ tau) :
    (H : ℝ) ^ 2 * ((v ^ 3 : ℕ) : ℝ) ^ tau ≤
      (((H * v) ^ 3 : ℕ) : ℝ) ^ tau := by
  have hexponent : (2 : ℝ) ≤ 3 * tau := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ H by exact_mod_cast hH) hexponent
  have hpow' : (H : ℝ) ^ 2 ≤ ((H : ℝ) ^ 3) ^ tau := by
    convert hpow using 1
    · exact (Real.rpow_natCast (H : ℝ) 2).symm
    · exact (Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ H) 3 tau).symm
  push_cast
  rw [mul_pow, Real.mul_rpow (by positivity) (by positivity)]
  exact mul_le_mul_of_nonneg_right hpow' (Real.rpow_nonneg (by positivity) tau)

/-- A matrix block retained in the paired tensor gives a square block in
sixfold symmetrization, with the full quadratic multiplicity weight. -/
theorem mme_sixSymmetrization_aggregate_matrix_extraction
    {K : Type u} [Field K] (T : TensorObj K 3)
    (n m p H v : ℕ) (hH : 1 ≤ H) (hvolume : n * m * p = H * v)
    (tau : ℝ) (htau : (2 : ℝ) / 3 ≤ tau)
    (hrestrict : TensorObj.Restrict (MMObj K n m p)
      (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T))) :
    TensorObj.Restrict (MMObj K (H * v) (H * v) (H * v))
      (sixSymmetrization T) ∧
    (H : ℝ) ^ 2 * ((v ^ 3 : ℕ) : ℝ) ^ tau ≤
      (((H * v) ^ 3 : ℕ) : ℝ) ^ tau := by
  constructor
  · have h := (mme_MMObj_cyclicSymmetrization_iso (K := K) n m p).2.trans
      ((mme_cyclicSymmetrization_mono_restrict hrestrict).trans
        (mme_sixSymmetrization_isomorphic_cyclic_paired_swap T).2)
    simpa only [hvolume] using h
  · exact mme_aggregate_matrix_volume_weight H v hH tau htau

/-- Retaining one aggregate matrix block per outer fiber gives the cubic
outer multiplicity and quadratic inner multiplicity simultaneously. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    (A H v : ℕ) (hH : 1 ≤ H) (tau : ℝ) (htau : (2 : ℝ) / 3 ≤ tau)
    (a b c : Fin A → ℕ) (hvolume : ∀ i, a i * b i * c i = H * v)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
      (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T))) :
    ∃ (Q : ℕ) (a' b' c' : Fin Q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization T) ∧
      (A : ℝ) ^ 3 * (H : ℝ) ^ 2 * ((v ^ 3 : ℕ) : ℝ) ^ tau ≤
        ∑ j, (((a' j * b' j * c' j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨Q, a', b', c', hQ, hiso, hvol⟩ :=
    mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume
      (K := K) a b c hvolume
  refine ⟨Q, a', b', c', ?_, ?_⟩
  · exact hiso.1.trans
      ((mme_cyclicSymmetrization_mono_restrict hrestrict).trans
        (mme_sixSymmetrization_isomorphic_cyclic_paired_swap T).2)
  · have hweighted := mul_le_mul_of_nonneg_left
      (mme_aggregate_matrix_volume_weight H v hH tau htau)
      (by positivity : (0 : ℝ) ≤ (A : ℝ) ^ 3)
    simp only [hvol, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hQ, Nat.cast_pow]
    simpa only [Nat.cast_pow, mul_assoc] using hweighted
