-- Prove2me | solution 1 for mme_dwz_prescribed_z_six_finite_restriction_witness_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T07:01:13.43972+00:00
-- url     : https://prove2.me/submissions/dc9255fd-c58d-4d6f-8d18-0847fbde1853

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_dwz_prescribed_z_power_repetition_restrict
import Theorems.Thm_mme_bigAdd_MM_kronPow_tau_flatten
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m r : ℕ) (tau v : ℝ)
    (h : SixFiniteWitness TensorObj.Restrict
      (prescribedZPower T bZ grade p m) (p.length m) tau v) :
    SixFiniteWitness TensorObj.Restrict
      (prescribedZPower T bZ grade p (m * r)) (p.length (m * r)) tau v := by
  obtain ⟨k, a, b, c, hrestrict, hweight⟩ := h
  obtain ⟨q, A, B, C, hflatten, hweightPower⟩ :=
    mme_bigAdd_MM_kronPow_tau_flatten (K := K) a b c tau (r := r)
  refine ⟨q, A, B, C, ?_, ?_⟩
  · exact hflatten.trans ((mme_restrict_kronPow hrestrict r).trans
      ((mme_sixSymmetrization_kronPow_isomorphic
        (prescribedZPower T bZ grade p m) r).1.trans
        (mme_sixSymmetrization_restrict
          (mme_dwz_prescribed_z_power_repetition_restrict T bZ grade p m r))))
  · have hnonneg : 0 ≤ v ^ (6 * p.length m) := by
      rw [show 6 * p.length m = (3 * p.length m) * 2 by omega, pow_mul]
      exact sq_nonneg _
    calc
      v ^ (6 * p.length (m * r)) = (v ^ (6 * p.length m)) ^ r := by
        rw [← pow_mul]
        congr 1
        simp only [IntegerZSplitProfile.length]
        ring
      _ ≤ (∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) ^ r :=
        pow_le_pow_left₀ hnonneg hweight r
      _ = ∑ j, (((A j * B j * C j : ℕ) : ℝ) ^ tau) := hweightPower.symm
