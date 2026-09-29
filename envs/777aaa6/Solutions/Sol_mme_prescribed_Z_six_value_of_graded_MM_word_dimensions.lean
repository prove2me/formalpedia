-- Prove2me | solution 1 for mme_prescribed_Z_six_value_of_graded_MM_word_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:50:14.292988+00:00
-- url     : https://prove2.me/submissions/73a8ef81-acba-4b9a-a297-3121f8b40d84

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_MMObj_isomorphic
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Tactic

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module Filter
open scoped BigOperators Classical
universe u
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

private def dimension {t : ℕ} (p : IntegerZSplitProfile t) (d : Fin t → ℕ) (m : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (fun a : Fin t ↦ p.count a * m) * ∏ a, d a ^ (p.count a * m)

private noncomputable def profile {t : ℕ} (p : IntegerZSplitProfile t) (a : Fin t) : ℝ :=
  (p.count a : ℝ) / p.denominator

private noncomputable def entropy {t : ℕ} (p : IntegerZSplitProfile t) : ℝ :=
  ∑ a : Fin t, Real.negMulLog (profile p a)

private noncomputable def exponent {t : ℕ} (p : IntegerZSplitProfile t) (d : Fin t → ℕ) : ℝ :=
  entropy p + ∑ a, profile p a * Real.log (d a)

private theorem entropy_eq {t : ℕ} (p : IntegerZSplitProfile t) :
    Real.log 2 * mme_modern_entropyBits (profile p) = entropy p := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold mme_modern_entropyBits entropy
  rw [mul_comm, div_mul_cancel₀ _ hlog]

private theorem dimension_entropy_polynomial_lower
    {t : ℕ} (p : IntegerZSplitProfile t) (d : Fin t → ℕ) (hd : ∀ a, 0 < d a) (m : ℕ) (hm : 0 < m) :
    Real.exp ((p.length m : ℝ) * exponent p d) ≤
      (6 * (((p.length m + 1 : ℕ) : ℝ))) ^ t * (dimension p d m : ℝ) := by
  have htotal : 0 < ∑ a : Fin t, p.count a := by
    rw [p.count_sum]
    exact p.denominator_pos
  have h := mme_dwz_multinomial_entropy_polynomial_lower p.count m hm htotal
  rw [p.count_sum] at h
  simp only [Fintype.card_fin] at h
  change Real.exp ((m : ℝ) * ((p.denominator : ℝ) * Real.log 2 *
      mme_modern_entropyBits (profile p))) ≤
    (6 * (((p.length m + 1 : ℕ) : ℝ))) ^ t *
      (Nat.multinomial Finset.univ (fun a ↦ p.count a * m) : ℝ) at h
  have harg : (m : ℝ) * ((p.denominator : ℝ) * Real.log 2 *
      mme_modern_entropyBits (profile p)) = (p.length m : ℝ) * entropy p := by
    rw [← entropy_eq]
    simp only [IntegerZSplitProfile.length, Nat.cast_mul]
    ring
  rw [harg] at h
  have hpow : Real.exp ((p.length m : ℝ) *
      ∑ a, profile p a * Real.log (d a)) =
      ((∏ a, d a ^ (p.count a * m) : ℕ) : ℝ) := by
    rw [Finset.mul_sum, Real.exp_sum, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro a _
    have harg : (p.length m : ℝ) * (profile p a * Real.log (d a)) =
        ((p.count a * m : ℕ) : ℝ) * Real.log (d a) := by
      have hden : (p.denominator : ℝ) ≠ 0 := by exact_mod_cast p.denominator_pos.ne'
      dsimp [profile, IntegerZSplitProfile.length]
      push_cast
      field_simp
    rw [harg, Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hd a), Nat.cast_pow]
  have hfactor : Real.exp ((p.length m : ℝ) * exponent p d) =
      Real.exp ((p.length m : ℝ) * entropy p) *
        ((∏ a, d a ^ (p.count a * m) : ℕ) : ℝ) := by
    rw [← hpow, ← Real.exp_add]
    congr 1
    unfold exponent
    ring
  rw [hfactor, dimension]
  push_cast
  simpa only [Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc] using
    mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (∏ a, d a ^ (p.count a * m) : ℕ))


private theorem scalar_rate
    {t : ℕ} (p : IntegerZSplitProfile t) (d : Fin t → ℕ) (hd : ∀ a, 0 < d a) (tau : ℝ) (htau : 0 < tau)
    (v : ℝ) (hv : 0 < v) (hstrict : v < Real.exp (tau * exponent p d)) :
    ∀ᶠ m : ℕ in atTop, v ^ p.length m ≤ (dimension p d m : ℝ) ^ tau := by
  let delta := tau * exponent p d - Real.log v
  have hdelta : 0 < delta := by
    have hlog := Real.log_lt_log hv hstrict
    rw [Real.log_exp] at hlog
    exact sub_pos.mpr hlog
  have habs := mme_log_sqrt_loss_eventually_le_linear
    ((t : ℝ) * tau) 0 ((t : ℝ) * tau * Real.log 6) delta hdelta
  obtain ⟨M, hM⟩ := eventually_atTop.1 habs
  filter_upwards [eventually_ge_atTop (max M 1)] with m hm
  have hmpos : 0 < m := by omega
  have hmN : m ≤ p.length m := by
    simpa [IntegerZSplitProfile.length] using
      Nat.mul_le_mul_right m (show 1 ≤ p.denominator from p.denominator_pos)
  have hMN : M ≤ p.length m := by omega
  have hsmall := hM (p.length m) hMN
  simp only [zero_mul, add_zero] at hsmall
  have hpoly := dimension_entropy_polynomial_lower p d hd m hmpos
  have hP : 0 < (6 * (((p.length m + 1 : ℕ) : ℝ))) ^ t := by positivity
  have hD : 0 < (dimension p d m : ℝ) :=
    pos_of_mul_pos_right ((Real.exp_pos _).trans_le hpoly) hP.le
  have hlog := Real.log_le_log (Real.exp_pos _) hpoly
  rw [Real.log_exp, Real.log_mul hP.ne' hD.ne', Real.log_pow,
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by positivity)] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogtau := mul_le_mul_of_nonneg_left hlog htau.le
  have hfinal : (p.length m : ℝ) * Real.log v ≤ Real.log (dimension p d m : ℝ) * tau := by
    dsimp only [delta] at hsmall
    push_cast at hlogtau
    nlinarith only [hlogtau, hsmall]
  rw [Real.rpow_def_of_pos hD]
  calc
    v ^ p.length m = Real.exp ((p.length m : ℝ) * Real.log v) := by
      rw [Real.exp_nat_mul, Real.exp_log hv]
    _ ≤ Real.exp (Real.log (dimension p d m : ℝ) * tau) := Real.exp_le_exp.mpr hfinal


private theorem bigAdd_one_isomorphic
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.bigAdd (fun _ : Fin 1 ↦ T)) T := by
  apply (TensorQ.toQ_eq_iff).1
  rw [TensorQ.toQ_bigAdd]
  simp


private theorem oneMM_six_restrict
    {K : Type u} [Field K] {Y : TensorObj K 3} (D : ℕ)
    (h : TensorObj.Restrict (MMObj K 1 1 D) Y ∨
      TensorObj.Restrict (MMObj K D 1 1) Y) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin 1 ↦ MMObj K (D ^ 2) (D ^ 2) (D ^ 2)))
      (sixSymmetrization Y) := by
  rcases h with h | h
  · have hiso := mme_sixSymmetrization_MMObj_isomorphic (K := K) 1 1 D
    simp only [one_mul] at hiso
    exact (bigAdd_one_isomorphic _).1.trans
      (hiso.2.trans (mme_sixSymmetrization_restrict h))
  · have hiso := mme_sixSymmetrization_MMObj_isomorphic (K := K) D 1 1
    simp only [mul_one] at hiso
    exact (bigAdd_one_isomorphic _).1.trans
      (hiso.2.trans (mme_sixSymmetrization_restrict h))

private theorem finite_six
    {K : Type u} [Field K] (T : TensorObj K 3)
    {t : ℕ} {I : Type u} (bZ : Basis I K (T.V 2)) (grade : I → Fin t)
    (p : IntegerZSplitProfile t) (d : Fin t → ℕ) (m : ℕ) (tau v : ℝ) (hv : 0 ≤ v)
    (hsource :
      TensorObj.Restrict (MMObj K 1 1 (dimension p d m))
        (prescribedZPower T bZ grade p m) ∨
      TensorObj.Restrict (MMObj K (dimension p d m) 1 1)
        (prescribedZPower T bZ grade p m))
    (hweight : v ^ p.length m ≤ (dimension p d m : ℝ) ^ tau) :
    SixFiniteWitness TensorObj.Restrict (prescribedZPower T bZ grade p m)
      (p.length m) tau v := by
  let D := dimension p d m
  refine ⟨1, (fun _ ↦ D ^ 2), (fun _ ↦ D ^ 2), (fun _ ↦ D ^ 2),
    oneMM_six_restrict D hsource, ?_⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  calc
    v ^ (6 * p.length m) = (v ^ p.length m) ^ 6 := by
      rw [← pow_mul, Nat.mul_comm]
    _ ≤ ((D : ℝ) ^ tau) ^ 6 := pow_le_pow_left₀ (pow_nonneg hv _) hweight 6
    _ = (((D ^ 2) * (D ^ 2) * (D ^ 2) : ℕ) : ℝ) ^ tau := by
      rw [Real.rpow_pow_comm (Nat.cast_nonneg D) tau 6]
      congr 1
      push_cast
      ring

private theorem value_of_finite
    {K : Type u} [Field K] (T : TensorObj K 3)
    {t : ℕ} {I : Type u} (bZ : Basis I K (T.V 2)) (grade : I → Fin t)
    (p : IntegerZSplitProfile t) (d : Fin t → ℕ) (hd : ∀ a, 0 < d a) (tau : ℝ) (htau : 0 < tau)
    (hsource : ∀ m,
      TensorObj.Restrict (MMObj K 1 1 (dimension p d m))
        (prescribedZPower T bZ grade p m) ∨
      TensorObj.Restrict (MMObj K (dimension p d m) 1 1)
        (prescribedZPower T bZ grade p m)) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau
      (Real.exp (tau * exponent p d)) := by
  unfold HasPrescribedZSixRestrictionValueAtLeast HasSixSequenceRate
  refine ⟨(Real.exp_pos _).le, ?_⟩
  intro v hv hstrict cutoff
  obtain ⟨M, hM⟩ := eventually_atTop.1 (scalar_rate p d hd tau htau v hv hstrict)
  refine ⟨max M cutoff, le_max_right _ _, ?_, ?_⟩
  · calc
      cutoff ≤ max M cutoff := le_max_right _ _
      _ ≤ p.length (max M cutoff) := by
        simpa [IntegerZSplitProfile.length] using
          Nat.mul_le_mul_right (max M cutoff)
            (show 1 ≤ p.denominator from p.denominator_pos)
  · exact finite_six T bZ grade p d (max M cutoff) tau v hv.le
      (hsource _) (hM (max M cutoff) (le_max_left _ _))


theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    {t : ℕ} {I : Type u} (bZ : Basis I K (T.V 2)) (grade : I → Fin t)
    (p : IntegerZSplitProfile t) (d : Fin t → ℕ) (hd : ∀ a, 0 < d a)
    (tau : ℝ) (htau : 0 < tau)
    (hsource : ∀ m,
      let D := Nat.multinomial Finset.univ (fun a ↦ p.count a * m) *
        ∏ a, d a ^ (p.count a * m)
      TensorObj.Restrict (MMObj K 1 1 D) (prescribedZPower T bZ grade p m) ∨
      TensorObj.Restrict (MMObj K D 1 1) (prescribedZPower T bZ grade p m)) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau
      (Real.exp (tau * ((∑ a, Real.negMulLog ((p.count a : ℝ) / p.denominator)) +
        ∑ a, ((p.count a : ℝ) / p.denominator) * Real.log (d a)))) := by
  exact value_of_finite T bZ grade p d hd tau htau hsource
