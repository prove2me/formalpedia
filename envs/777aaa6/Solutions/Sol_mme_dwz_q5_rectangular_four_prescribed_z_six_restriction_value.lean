-- Prove2me | solution 1 for mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T09:35:50.348266+00:00
-- url     : https://prove2.me/submissions/de623b03-d085-4010-b7dd-1c9d7df6d0a6

import Theorems.Thm_mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions
import Theorems.Thm_mme_dwz_q5_odd_coarse_prescribed_z_word_card
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
set_option warningAsError true
set_option maxHeartbeats 2000000

private def dimension (p : IntegerZSplitProfile 3) (m : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (fun a : Fin 3 ↦ p.count a * m) * 5 ^ p.length m

private noncomputable def profile (p : IntegerZSplitProfile 3) (a : Fin 3) : ℝ :=
  (p.count a : ℝ) / p.denominator

private noncomputable def entropy (p : IntegerZSplitProfile 3) : ℝ :=
  ∑ a : Fin 3, Real.negMulLog (profile p a)

private noncomputable def exponent (p : IntegerZSplitProfile 3) : ℝ :=
  entropy p + Real.log 5

private theorem entropy_eq (p : IntegerZSplitProfile 3) :
    Real.log 2 * mme_modern_entropyBits (profile p) = entropy p := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold mme_modern_entropyBits entropy
  rw [mul_comm, div_mul_cancel₀ _ hlog]

private theorem dimension_entropy_polynomial_lower
    (p : IntegerZSplitProfile 3) (m : ℕ) (hm : 0 < m) :
    Real.exp ((p.length m : ℝ) * exponent p) ≤
      (6 * (((p.length m + 1 : ℕ) : ℝ))) ^ 3 * (dimension p m : ℝ) := by
  have htotal : 0 < ∑ a : Fin 3, p.count a := by
    rw [p.count_sum]
    exact p.denominator_pos
  have h := mme_dwz_multinomial_entropy_polynomial_lower p.count m hm htotal
  rw [p.count_sum] at h
  simp only [Fintype.card_fin] at h
  change Real.exp ((m : ℝ) * ((p.denominator : ℝ) * Real.log 2 *
      mme_modern_entropyBits (profile p))) ≤
    (6 * (((p.length m + 1 : ℕ) : ℝ))) ^ 3 *
      (Nat.multinomial Finset.univ (fun a ↦ p.count a * m) : ℝ) at h
  have harg : (m : ℝ) * ((p.denominator : ℝ) * Real.log 2 *
      mme_modern_entropyBits (profile p)) = (p.length m : ℝ) * entropy p := by
    rw [← entropy_eq]
    simp only [IntegerZSplitProfile.length, Nat.cast_mul]
    ring
  rw [harg] at h
  have hpow : Real.exp ((p.length m : ℝ) * Real.log 5) =
      ((5 ^ p.length m : ℕ) : ℝ) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    norm_cast
  have hfactor : Real.exp ((p.length m : ℝ) * exponent p) =
      Real.exp ((p.length m : ℝ) * entropy p) * ((5 ^ p.length m : ℕ) : ℝ) := by
    rw [← hpow, ← Real.exp_add]
    congr 1
    unfold exponent
    ring
  rw [hfactor, dimension]
  push_cast
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc] using
    mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (5 ^ p.length m : ℕ))

private theorem scalar_rate
    (p : IntegerZSplitProfile 3) (tau : ℝ) (htau : 0 < tau)
    (v : ℝ) (hv : 0 < v) (hstrict : v < Real.exp (tau * exponent p)) :
    ∀ᶠ m : ℕ in atTop, v ^ p.length m ≤ (dimension p m : ℝ) ^ tau := by
  let delta := tau * exponent p - Real.log v
  have hdelta : 0 < delta := by
    have hlog := Real.log_lt_log hv hstrict
    rw [Real.log_exp] at hlog
    exact sub_pos.mpr hlog
  have habs := mme_log_sqrt_loss_eventually_le_linear
    (3 * tau) 0 (3 * tau * Real.log 6) delta hdelta
  obtain ⟨M, hM⟩ := eventually_atTop.1 habs
  filter_upwards [eventually_ge_atTop (max M 1)] with m hm
  have hmpos : 0 < m := by omega
  have hmN : m ≤ p.length m := by
    simpa [IntegerZSplitProfile.length] using
      Nat.mul_le_mul_right m (show 1 ≤ p.denominator from p.denominator_pos)
  have hMN : M ≤ p.length m := by omega
  have hsmall := hM (p.length m) hMN
  simp only [zero_mul, add_zero] at hsmall
  have hpoly := dimension_entropy_polynomial_lower p m hmpos
  have hP : 0 < (6 * (((p.length m + 1 : ℕ) : ℝ))) ^ 3 := by positivity
  have hD : 0 < (dimension p m : ℝ) :=
    pos_of_mul_pos_right ((Real.exp_pos _).trans_le hpoly) hP.le
  have hlog := Real.log_le_log (Real.exp_pos _) hpoly
  rw [Real.log_exp, Real.log_mul hP.ne' hD.ne', Real.log_pow,
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by positivity)] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogtau := mul_le_mul_of_nonneg_left hlog htau.le
  have hfinal : (p.length m : ℝ) * Real.log v ≤ Real.log (dimension p m : ℝ) * tau := by
    dsimp only [delta] at hsmall
    push_cast at hlogtau
    nlinarith only [hlogtau, hsmall]
  rw [Real.rpow_def_of_pos hD]
  calc
    v ^ p.length m = Real.exp ((p.length m : ℝ) * Real.log v) := by
      rw [Real.exp_nat_mul, Real.exp_log hv]
    _ ≤ Real.exp (Real.log (dimension p m : ℝ) * tau) := Real.exp_le_exp.mpr hfinal


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
    {I : Type u} (bZ : Basis I K (T.V 2)) (grade : I → Fin 3)
    (p : IntegerZSplitProfile 3) (m : ℕ) (tau v : ℝ) (hv : 0 ≤ v)
    (hsource :
      TensorObj.Restrict (MMObj K 1 1 (dimension p m))
        (prescribedZPower T bZ grade p m) ∨
      TensorObj.Restrict (MMObj K (dimension p m) 1 1)
        (prescribedZPower T bZ grade p m))
    (hweight : v ^ p.length m ≤ (dimension p m : ℝ) ^ tau) :
    SixFiniteWitness TensorObj.Restrict (prescribedZPower T bZ grade p m)
      (p.length m) tau v := by
  let D := dimension p m
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
    {I : Type u} (bZ : Basis I K (T.V 2)) (grade : I → Fin 3)
    (p : IntegerZSplitProfile 3) (tau : ℝ) (htau : 0 < tau)
    (hsource : ∀ m,
      TensorObj.Restrict (MMObj K 1 1 (dimension p m))
        (prescribedZPower T bZ grade p m) ∨
      TensorObj.Restrict (MMObj K (dimension p m) 1 1)
        (prescribedZPower T bZ grade p m)) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau
      (Real.exp (tau * ∑ a : Fin 3, Real.negMulLog
        ((p.count a : ℝ) / p.denominator)) * (5 : ℝ) ^ tau) := by
  have hbase :
      (Real.exp (tau * ∑ a : Fin 3, Real.negMulLog
        ((p.count a : ℝ) / p.denominator)) * (5 : ℝ) ^ tau) =
      Real.exp (tau * exponent p) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5), ← Real.exp_add]
    congr 1
    unfold exponent entropy profile
    ring
  rw [hbase]
  unfold HasPrescribedZSixRestrictionValueAtLeast HasSixSequenceRate
  refine ⟨(Real.exp_pos _).le, ?_⟩
  intro v hv hstrict cutoff
  obtain ⟨M, hM⟩ := eventually_atTop.1 (scalar_rate p tau htau v hv hstrict)
  refine ⟨max M cutoff, le_max_right _ _, ?_, ?_⟩
  · calc
      cutoff ≤ max M cutoff := le_max_right _ _
      _ ≤ p.length (max M cutoff) := by
        simpa [IntegerZSplitProfile.length] using
          Nat.mul_le_mul_right (max M cutoff)
            (show 1 ≤ p.denominator from p.denominator_pos)
  · exact finite_six T bZ grade p (max M cutoff) tau v hv.le
      (hsource _) (hM (max M cutoff) (le_max_left _ _))

theorem solution (K : Type u) [Field K] (p : IntegerZSplitProfile 3)
    (tau : ℝ) (htau : 0 < tau) :
    let V := Real.exp (tau * ∑ a : Fin 3, Real.negMulLog
      ((p.count a : ℝ) / p.denominator)) * (5 : ℝ) ^ tau
    (p.count 0 = 0 →
      HasPrescribedZSixRestrictionValueAtLeast
        ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 1 3))
        ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p tau V) ∧
    (p.count 2 = 0 →
      HasPrescribedZSixRestrictionValueAtLeast
        ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 3 1))
        ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p tau V) ∧
    (p.count 0 = 0 →
      HasPrescribedZSixRestrictionValueAtLeast
        ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 1 0 3))
        ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p tau V) ∧
    (p.count 2 = 0 →
      HasPrescribedZSixRestrictionValueAtLeast
        ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 3 0 1))
        ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
        LiftedCoarsePair.leftGrade p tau V) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hp
    apply value_of_finite _ _ _ p tau htau
    intro m
    have hf := (mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions K p m).1
    rw [(mme_dwz_q5_odd_coarse_prescribed_z_word_card p m).2 hp] at hf
    exact Or.inl hf
  · intro hp
    apply value_of_finite _ _ _ p tau htau
    intro m
    have hf := (mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions K p m).2.1
    rw [(mme_dwz_q5_odd_coarse_prescribed_z_word_card p m).1 hp] at hf
    exact Or.inl hf
  · intro hp
    apply value_of_finite _ _ _ p tau htau
    intro m
    have hf := (mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions K p m).2.2.1
    rw [(mme_dwz_q5_odd_coarse_prescribed_z_word_card p m).2 hp] at hf
    exact Or.inr hf
  · intro hp
    apply value_of_finite _ _ _ p tau htau
    intro m
    have hf := (mme_dwz_q5_rectangular_four_prescribed_z_finite_restrictions K p m).2.2.2
    rw [(mme_dwz_q5_odd_coarse_prescribed_z_word_card p m).1 hp] at hf
    exact Or.inr hf
