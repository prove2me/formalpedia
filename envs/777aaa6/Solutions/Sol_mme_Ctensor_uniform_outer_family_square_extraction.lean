-- Prove2me | solution 1 for mme_Ctensor_uniform_outer_family_square_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:16:52.931761+00:00
-- url     : https://prove2.me/submissions/f25b4f69-1494-4ced-9c9d-05c8893423bc

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_CTensorThreeCyclicBalancedGradingCertificate
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Theorems.Thm_mme_Ctensor_uniform_three_star_square_extraction
import Theorems.Thm_mme_Ctensor_outer_triple_distribution
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested
import Mathlib.Tactic

open MME BigOperators
universe u
set_option autoImplicit false

/-- Uniform matrix leaves give a family of square blocks with the full outer-triple count. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (m n p : ℕ)
    (hdims : ∀ a h, (stars.certificate a).m h = m ∧
      (stars.certificate a).n h = n ∧ (stars.certificate a).p h = p)
    (hH : 0 < H) :
    ∃ k : ℕ,
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin k ↦ MMObj K (m * n * p) (m * n * p) (m * n * p)))
        (cyclicSymmetrization T) ∧
      (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
        Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))) ≤ (k : ℝ) := by
  classical
  let I := Fin A × Fin A × Fin A
  let count := Fintype.card I
  let enum : I ≃ Fin count := Fintype.equivFin I
  let block : Fin count → TensorObj K 3 := fun j ↦
    let a := enum.symm j
    threeStarCyclicProduct (stars.star a.1) (stars.star a.2.1) (stars.star a.2.2)
  let M := MMObj K (m * n * p) (m * n * p) (m * n * p)
  let lower : ℝ := (H : ℝ) ^ 2 *
    Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))
  let q := Nat.ceil lower
  have hlower : lower ≤ (q : ℝ) := Nat.le_ceil lower
  have hrestrict : ∀ j : Fin count,
      TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin q ↦ M)) (block j) := by
    intro j
    let a := enum.symm j
    obtain ⟨k, hr, hk⟩ := mme_Ctensor_uniform_three_star_square_extraction
      (stars.certificate a.1) (stars.certificate a.2.1) (stars.certificate a.2.2)
      m n p (hdims a.1) (hdims a.2.1) (hdims a.2.2) hH
    have hq : q ≤ k := Nat.ceil_le.mpr hk
    have hpref := mme_bigAdd_prefix_restrict (K := K) (d := 3)
      (by omega) hq (fun _ : Fin k ↦ M)
    exact hpref.trans hr
  have hnested : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin count ↦ TensorObj.bigAdd (fun _ : Fin q ↦ M)))
      (TensorObj.bigAdd block) := mme_bigAdd_mono_restrict hrestrict
  have hflat : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (count * q) ↦ M)) (TensorObj.bigAdd block) :=
    (mme_bigAdd_fin_mul_isomorphic_nested (fun (_ : Fin count) (_ : Fin q) ↦ M)).1.trans
      hnested
  have hdist : TensorObj.Restrict (TensorObj.bigAdd block)
      (cyclicSymmetrization (TensorObj.bigAdd stars.star)) := by
    simpa only [I, count, enum, block] using mme_Ctensor_outer_triple_distribution stars.star
  refine ⟨count * q, hflat.trans (hdist.trans
    (mme_cyclicSymmetrization_mono_restrict stars.restrict)), ?_⟩
  have hcount : count = A ^ 3 := by simp [count, I, pow_three]
  change (A : ℝ) ^ 3 * lower ≤ ((count * q : ℕ) : ℝ)
  rw [Nat.cast_mul, hcount, Nat.cast_pow]
  exact mul_le_mul_of_nonneg_left hlower (by positivity)

#print axioms solution
