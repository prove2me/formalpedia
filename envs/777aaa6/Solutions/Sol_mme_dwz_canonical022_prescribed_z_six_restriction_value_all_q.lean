-- Prove2me | solution 1 for mme_dwz_canonical022_prescribed_z_six_restriction_value_all_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:40:14.302088+00:00
-- url     : https://prove2.me/submissions/2072604a-73bb-484a-a7d6-08761595d899

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Theorems.Thm_mme_dwz_canonical022_prescribed_z_MM_restriction
import Theorems.Thm_mme_dwz_canonical022_prescribed_z_word_card_general
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_MMObj_isomorphic
import Definitions.Def_mme_rank_bridge

open MME MME.DWZFineChannel MME.DWZComponentRestriction MME.DWZRestrictedValue Module Filter
open scoped BigOperators Classical

universe u

set_option autoImplicit false
set_option warningAsError true

private def dimension (q : ℕ) (p : IntegerZSplitProfile 3) (m : ℕ) : ℕ :=
  Nat.choose (p.length m) (p.count 0 * m) *
    Nat.choose (p.length m - p.count 0 * m) (p.count 2 * m) *
      q ^ (2 * (p.count 1 * m))

private noncomputable def profile (p : IntegerZSplitProfile 3) (a : Fin 3) : ℝ :=
  (p.count a : ℝ) / p.denominator

private noncomputable def entropy (p : IntegerZSplitProfile 3) : ℝ :=
  ∑ a : Fin 3, Real.negMulLog (profile p a)

private noncomputable def exponent (q : ℕ) (p : IntegerZSplitProfile 3) : ℝ :=
  entropy p + 2 * profile p 1 * Real.log (q : ℝ)

private theorem multinomial_three_choose (A B C : ℕ) :
    Nat.multinomial Finset.univ ![A, B, C] =
      Nat.choose (A + B + C) A * Nat.choose (B + C) C := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have h : Nat.multinomial Finset.univ ![A, B, C] =
      Nat.choose (A + B + C) A * Nat.choose (B + C) B := by
    rw [huniv, Nat.multinomial_insert (by decide), Nat.binomial_eq_choose (by decide)]
    simp [Nat.add_assoc]
  rw [h, Nat.choose_symm_add]

private theorem dimension_eq_multinomial (q : ℕ) (p : IntegerZSplitProfile 3) (m : ℕ) :
    dimension q p m =
      Nat.multinomial Finset.univ (fun a : Fin 3 ↦ p.count a * m) *
        q ^ (2 * (p.count 1 * m)) := by
  have hv : (fun a : Fin 3 ↦ p.count a * m) =
      ![p.count 0 * m, p.count 1 * m, p.count 2 * m] := by
    funext a
    fin_cases a <;> rfl
  have hsum : p.count 0 + p.count 1 + p.count 2 = p.denominator := by
    simpa only [Fin.sum_univ_succ, Nat.add_zero, Nat.add_assoc] using p.count_sum
  have hlen : p.length m = p.count 0 * m + p.count 1 * m + p.count 2 * m := by
    unfold IntegerZSplitProfile.length
    rw [← hsum]
    ring
  rw [dimension, hv, multinomial_three_choose, hlen]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left]

private theorem entropy_eq (p : IntegerZSplitProfile 3) :
    Real.log 2 * mme_modern_entropyBits (profile p) = entropy p := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold mme_modern_entropyBits entropy
  rw [mul_comm, div_mul_cancel₀ _ hlog]

private theorem dimension_entropy_polynomial_lower
    (q : ℕ) (hq : 0 < q) (p : IntegerZSplitProfile 3) (m : ℕ) (hm : 0 < m) :
    Real.exp ((p.length m : ℝ) * exponent q p) ≤
      (6 * (((p.length m + 1 : ℕ) : ℝ))) ^ 3 * (dimension q p m : ℝ) := by
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
  have hd : (p.denominator : ℝ) ≠ 0 := by exact_mod_cast p.denominator_pos.ne'
  have hmean : (p.length m : ℝ) * profile p 1 = (p.count 1 * m : ℕ) := by
    simp only [IntegerZSplitProfile.length, profile, Nat.cast_mul]
    field_simp [hd]
  have hpow : Real.exp (((2 * (p.count 1 * m) : ℕ) : ℝ) * Real.log (q : ℝ)) =
      ((q ^ (2 * (p.count 1 * m)) : ℕ) : ℝ) := by
    rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hq : (0 : ℝ) < q)]
    norm_cast
  have hfactor : Real.exp ((p.length m : ℝ) * exponent q p) =
      Real.exp ((p.length m : ℝ) * entropy p) *
        ((q ^ (2 * (p.count 1 * m)) : ℕ) : ℝ) := by
    rw [← hpow, ← Real.exp_add]
    congr 1
    unfold exponent
    calc
      (p.length m : ℝ) * (entropy p + 2 * profile p 1 * Real.log (q : ℝ)) =
          (p.length m : ℝ) * entropy p +
            2 * ((p.length m : ℝ) * profile p 1) * Real.log (q : ℝ) := by ring
      _ = (p.length m : ℝ) * entropy p +
          ((2 * (p.count 1 * m) : ℕ) : ℝ) * Real.log (q : ℝ) := by
        rw [hmean]
        push_cast
        ring
  rw [hfactor, dimension_eq_multinomial]
  push_cast
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc] using
    mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (q ^ (2 * (p.count 1 * m)) : ℕ))

private theorem scalar_rate
    (q : ℕ) (hq : 0 < q) (p : IntegerZSplitProfile 3) (tau : ℝ) (htau : 0 < tau)
    (v : ℝ) (hv : 0 < v) (hstrict : v < Real.exp (tau * exponent q p)) :
    ∀ᶠ m : ℕ in atTop, v ^ p.length m ≤ (dimension q p m : ℝ) ^ tau := by
  let delta := tau * exponent q p - Real.log v
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
  have hpoly := dimension_entropy_polynomial_lower q hq p m hmpos
  have hP : 0 < (6 * (((p.length m + 1 : ℕ) : ℝ))) ^ 3 := by positivity
  have hD : 0 < (dimension q p m : ℝ) :=
    pos_of_mul_pos_right ((Real.exp_pos _).trans_le hpoly) hP.le
  have hlog := Real.log_le_log (Real.exp_pos _) hpoly
  rw [Real.log_exp, Real.log_mul hP.ne' hD.ne', Real.log_pow,
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by positivity)] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogtau := mul_le_mul_of_nonneg_left hlog htau.le
  have hfinal : (p.length m : ℝ) * Real.log v ≤ Real.log (dimension q p m : ℝ) * tau := by
    dsimp only [delta] at hsmall
    push_cast at hlogtau
    nlinarith only [hlogtau, hsmall]
  rw [Real.rpow_def_of_pos hD]
  calc
    v ^ p.length m = Real.exp ((p.length m : ℝ) * Real.log v) := by
      rw [Real.exp_nat_mul, Real.exp_log hv]
    _ ≤ Real.exp (Real.log (dimension q p m : ℝ) * tau) := Real.exp_le_exp.mpr hfinal

private theorem bigAdd_one_isomorphic
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.bigAdd (fun _ : Fin 1 ↦ T)) T := by
  apply (TensorQ.toQ_eq_iff).1
  rw [TensorQ.toQ_bigAdd]
  simp

private theorem oneMM_six_restrict
    {K : Type u} [Field K] {Y : TensorObj K 3}
    (D : ℕ) (h : TensorObj.Restrict (MMObj K 1 1 D) Y) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin 1 ↦ MMObj K (D ^ 2) (D ^ 2) (D ^ 2)))
      (sixSymmetrization Y) := by
  have hiso := mme_sixSymmetrization_MMObj_isomorphic (K := K) 1 1 D
  simp only [one_mul] at hiso
  exact (bigAdd_one_isomorphic _).1.trans
    (hiso.2.trans (mme_sixSymmetrization_restrict h))

private theorem finite_six
    (K : Type u) [Field K] (q : ℕ) (p : IntegerZSplitProfile 3)
    (m : ℕ) (tau v : ℝ) (hv : 0 ≤ v) :
    let bZ : Basis (LiftedCoarsePair.{u} q 2) K ((Central022Block K q).V 2) :=
      (coarseClassBasis (K := K) q 2 2).reindex Equiv.ulift.symm
    let D := Nat.choose (p.length m) (p.count 0 * m) *
      Nat.choose (p.length m - p.count 0 * m) (p.count 2 * m) *
        q ^ (2 * (p.count 1 * m))
    v ^ (p.length m) ≤ (D : ℝ) ^ tau →
      SixFiniteWitness TensorObj.Restrict
        (prescribedZPower (Central022Block K q) bZ LiftedCoarsePair.leftGrade p m)
        (p.length m) tau v := by
  dsimp only
  intro hweight
  let D := Nat.choose (p.length m) (p.count 0 * m) *
    Nat.choose (p.length m - p.count 0 * m) (p.count 2 * m) *
      q ^ (2 * (p.count 1 * m))
  have hsource := mme_dwz_canonical022_prescribed_z_MM_restriction K q p m
  dsimp only at hsource
  rw [mme_dwz_canonical022_prescribed_z_word_card_general q p m] at hsource
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

theorem solution
    (K : Type u) [Field K] (q : ℕ) (hq : 0 < q) (p : IntegerZSplitProfile 3)
    (tau : ℝ) (htau : 0 < tau) :
    let bZ : Basis (LiftedCoarsePair.{u} q 2) K ((Central022Block K q).V 2) :=
      (coarseClassBasis (K := K) q 2 2).reindex Equiv.ulift.symm
    HasPrescribedZSixRestrictionValueAtLeast (Central022Block K q) bZ
      LiftedCoarsePair.leftGrade p tau
      (Real.exp (tau * ∑ a : Fin 3, Real.negMulLog
          ((p.count a : ℝ) / p.denominator)) *
        (q : ℝ) ^ (2 * tau * (p.count 1 : ℝ) / p.denominator)) := by
  dsimp only
  have hbase :
      (Real.exp (tau * ∑ a : Fin 3, Real.negMulLog
          ((p.count a : ℝ) / p.denominator)) *
        (q : ℝ) ^ (2 * tau * (p.count 1 : ℝ) / p.denominator)) =
      Real.exp (tau * exponent q p) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hq : (0 : ℝ) < q), ← Real.exp_add]
    congr 1
    unfold exponent entropy profile
    simp only [div_eq_mul_inv]
    ring
  rw [hbase]
  unfold HasPrescribedZSixRestrictionValueAtLeast HasSixSequenceRate
  refine ⟨(Real.exp_pos _).le, ?_⟩
  intro v hv hstrict cutoff
  obtain ⟨M, hM⟩ := eventually_atTop.1 (scalar_rate q hq p tau htau v hv hstrict)
  refine ⟨max M cutoff, le_max_right _ _, ?_, ?_⟩
  · calc
      cutoff ≤ max M cutoff := le_max_right _ _
      _ ≤ p.length (max M cutoff) := by
        simpa [IntegerZSplitProfile.length] using
          Nat.mul_le_mul_right (max M cutoff)
            (show 1 ≤ p.denominator from p.denominator_pos)
  · exact finite_six K q p (max M cutoff) tau v hv.le
      (hM (max M cutoff) (le_max_left _ _))
