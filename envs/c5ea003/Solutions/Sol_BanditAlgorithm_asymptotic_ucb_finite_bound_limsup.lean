-- Prove2me | solution 1 for BanditAlgorithm.asymptotic_ucb_finite_bound_limsup
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-20T17:00:44.96787+00:00
-- url     : https://prove2.me/submissions/7761ca31-cea6-4712-9e38-06f4429ab38f

import Definitions.Def_asymptoticUcbPolicy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.CompareExp
import Mathlib.Tactic.Linarith

open Filter Topology

namespace BanditAlgorithm

/-! Verified analytic infrastructure for the second child in the Theorem 8.1
reduction.  Source: Lattimore--Szepesvári, proof of Theorem 8.1, final sentence,
printed p. 120 / PDF p. 129. -/

lemma tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma one_le_asymptoticUcbSchedule (n : ℕ) :
    1 ≤ asymptoticUcbSchedule n := by
  rw [asymptoticUcbSchedule]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (Real.log (n : ℝ))))

lemma log_asymptoticUcbSchedule_nonneg (n : ℕ) :
    0 ≤ Real.log (asymptoticUcbSchedule n) :=
  Real.log_nonneg (one_le_asymptoticUcbSchedule n)

lemma asymptoticUcbSchedule_factorization (n : ℕ) (hn : 0 < n) :
    asymptoticUcbSchedule n =
      (n : ℝ) * ((n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2) := by
  simp [asymptoticUcbSchedule, mul_add, Nat.ne_of_gt hn]

lemma log_asymptoticUcbSchedule_factorization (n : ℕ) (hn : 0 < n) :
    Real.log (asymptoticUcbSchedule n) =
      Real.log (n : ℝ) +
        Real.log ((n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2) := by
  rw [asymptoticUcbSchedule_factorization n hn,
    Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  positivity

lemma tendsto_log_log_nat_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_log_nat_atTop).tendsto_div_nhds_zero

lemma tendsto_asymptoticUcbSchedule_atTop :
    Tendsto (fun n : ℕ ↦ asymptoticUcbSchedule n) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_nat_atTop
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hnat
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsquare : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  rw [asymptoticUcbSchedule]
  nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hsquare)]

lemma tendsto_log_asymptoticUcbSchedule_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (asymptoticUcbSchedule n)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_asymptoticUcbSchedule_atTop

lemma eventually_pos_log_asymptoticUcbSchedule :
    ∀ᶠ n : ℕ in atTop, 0 < Real.log (asymptoticUcbSchedule n) :=
  tendsto_log_asymptoticUcbSchedule_atTop.eventually_gt_atTop 0

lemma tendsto_inv_log_asymptoticUcbSchedule_zero :
    Tendsto (fun n : ℕ ↦ (Real.log (asymptoticUcbSchedule n))⁻¹)
      atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_asymptoticUcbSchedule_atTop

lemma tendsto_sqrt_log_asymptoticUcbSchedule_atTop :
    Tendsto (fun n : ℕ ↦ Real.sqrt (Real.log (asymptoticUcbSchedule n)))
      atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_log_asymptoticUcbSchedule_atTop

lemma tendsto_inv_sqrt_log_asymptoticUcbSchedule_zero :
    Tendsto
      (fun n : ℕ ↦ (Real.sqrt (Real.log (asymptoticUcbSchedule n)))⁻¹)
      atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_sqrt_log_asymptoticUcbSchedule_atTop

lemma tendsto_sqrt_pi_mul_inv_sqrt_log_asymptoticUcbSchedule_zero :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt Real.pi *
        (Real.sqrt (Real.log (asymptoticUcbSchedule n)))⁻¹)
      atTop (𝓝 0) :=
  by
    simpa using
      (tendsto_const_nhds (x := Real.sqrt Real.pi)).mul
        tendsto_inv_sqrt_log_asymptoticUcbSchedule_zero

lemma tendsto_sqrt_pi_log_schedule_div_log_schedule_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) /
          Real.log (asymptoticUcbSchedule n))
      atTop (𝓝 0) := by
  refine tendsto_sqrt_pi_mul_inv_sqrt_log_asymptoticUcbSchedule_zero.congr' ?_
  filter_upwards [eventually_pos_log_asymptoticUcbSchedule] with n hn
  rw [Real.sqrt_mul (le_of_lt Real.pi_pos), mul_div_assoc,
    Real.sqrt_div_self]

lemma tendsto_fourthRoot_log_asymptoticUcbSchedule_atTop :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt
        (Real.sqrt (Real.log (asymptoticUcbSchedule n))))
      atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_sqrt_log_asymptoticUcbSchedule_atTop

/-- The vanishing epsilon used in the last sentence of the proof of Theorem
8.1.  This is `log(f(n))^(-1/4)`; the remaining comparison
`log(f(n)) / log(n) → 1` identifies it with the book's displayed choice. -/
lemma tendsto_inv_fourthRoot_log_asymptoticUcbSchedule_zero :
    Tendsto
      (fun n : ℕ ↦
        (Real.sqrt (Real.sqrt (Real.log (asymptoticUcbSchedule n))))⁻¹)
      atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    tendsto_fourthRoot_log_asymptoticUcbSchedule_atTop

lemma eventually_pos_inv_fourthRoot_log_asymptoticUcbSchedule :
    ∀ᶠ n : ℕ in atTop,
      0 < (Real.sqrt
        (Real.sqrt (Real.log (asymptoticUcbSchedule n))))⁻¹ := by
  filter_upwards
    [tendsto_fourthRoot_log_asymptoticUcbSchedule_atTop.eventually_gt_atTop 0]
      with n hn
  exact inv_pos.mpr hn

lemma eventually_inv_fourthRoot_log_asymptoticUcbSchedule_lt
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (Real.sqrt
        (Real.sqrt (Real.log (asymptoticUcbSchedule n))))⁻¹ < δ :=
  (tendsto_order.1
    tendsto_inv_fourthRoot_log_asymptoticUcbSchedule_zero).2 δ hδ

lemma eventually_inv_fourthRoot_log_asymptoticUcbSchedule_admissible
    {k : ℕ} (Δ : Fin k → ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ i, 0 < Δ i →
      0 < (Real.sqrt
        (Real.sqrt (Real.log (asymptoticUcbSchedule n))))⁻¹ ∧
      (Real.sqrt
        (Real.sqrt (Real.log (asymptoticUcbSchedule n))))⁻¹ < Δ i := by
  rw [eventually_all]
  intro i
  by_cases hi : 0 < Δ i
  · filter_upwards
      [eventually_pos_inv_fourthRoot_log_asymptoticUcbSchedule,
        eventually_inv_fourthRoot_log_asymptoticUcbSchedule_lt hi]
        with n hnpos hnlt
    exact fun _ ↦ ⟨hnpos, hnlt⟩
  · exact Filter.Eventually.of_forall (fun _ hpos ↦ (hi hpos).elim)

noncomputable def asymptoticUcbEpsilon (n : ℕ) : ℝ :=
  (Real.sqrt (Real.sqrt (Real.log (asymptoticUcbSchedule n))))⁻¹

/-- Eq. (8.1) specialized, eventually, at the vanishing epsilon chosen in the
last sentence of the proof of Theorem 8.1. -/
lemma eventually_finite_bound_at_asymptoticUcbEpsilon
    {k : ℕ} (R : ℕ → ℝ) (Δ : Fin k → ℝ)
    (hR : ∀ (n : ℕ) (ε : Fin k → ℝ),
      (∀ i, 0 < Δ i → 0 < ε i ∧ ε i < Δ i) →
      R n ≤
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
          Δ i *
            (1 + 5 / (ε i) ^ 2 +
              2 / (Δ i - ε i) ^ 2 *
                (Real.log (asymptoticUcbSchedule n) +
                  Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1))) :
    ∀ᶠ n : ℕ in atTop,
      R n ≤
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
          Δ i *
            (1 + 5 / asymptoticUcbEpsilon n ^ 2 +
              2 / (Δ i - asymptoticUcbEpsilon n) ^ 2 *
                (Real.log (asymptoticUcbSchedule n) +
                  Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1)) := by
  filter_upwards
    [eventually_inv_fourthRoot_log_asymptoticUcbSchedule_admissible Δ]
      with n hn
  simpa [asymptoticUcbEpsilon] using
    hR n (fun _ ↦ asymptoticUcbEpsilon n) hn

lemma tendsto_inv_log_nat_zero :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop

lemma tendsto_log_two_div_log_nat_zero :
    Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds (x := Real.log 2)).mul tendsto_inv_log_nat_zero

lemma tendsto_two_mul_log_log_nat_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        2 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  convert
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      tendsto_log_log_nat_div_log_nat_zero using 1 <;> ring

lemma tendsto_log_two_log_sq_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.log (2 * Real.log (n : ℝ) ^ 2) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Real.log 2 / Real.log (n : ℝ) +
            2 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_log_two_div_log_nat_zero.add
      tendsto_two_mul_log_log_nat_div_log_nat_zero
  refine hsum.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hn
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (pow_ne_zero 2 (ne_of_gt hn)), Real.log_pow]
  ring

lemma tendsto_log_schedule_correction_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.log ((n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2) /
          Real.log (n : ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_log_two_log_sq_div_log_nat_zero
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
    have hsq : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
    have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    have hsum : 1 ≤ (n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2 := by linarith
    exact div_nonneg (Real.log_nonneg hsum) (by linarith)
  · filter_upwards [tendsto_log_nat_atTop.eventually_ge_atTop 1] with n hn
    have hn_ne : n ≠ 0 := by
      intro hn0
      subst n
      norm_num at hn
    have hn_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn_ne)
    have hn_cast_one : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn_ne
    have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn_cast_one
    have hsq : 1 ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
    have hsum_pos : 0 < (n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2 := by positivity
    have hsum_le :
        (n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2 ≤
          2 * Real.log (n : ℝ) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hsum_pos hsum_le) (by linarith)

lemma tendsto_log_asymptoticUcbSchedule_div_log_nat_one :
    Tendsto
      (fun n : ℕ ↦
        Real.log (asymptoticUcbSchedule n) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          1 +
            Real.log ((n : ℝ)⁻¹ + Real.log (n : ℝ) ^ 2) /
              Real.log (n : ℝ))
        atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      tendsto_log_schedule_correction_div_log_nat_zero
  refine hsum.congr' ?_
  filter_upwards [tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hn
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    norm_num at hn
  rw [log_asymptoticUcbSchedule_factorization n (Nat.pos_of_ne_zero hn_ne)]
  field_simp

lemma tendsto_asymptoticUcbEpsilon_zero :
    Tendsto asymptoticUcbEpsilon atTop (𝓝 0) := by
  simpa [asymptoticUcbEpsilon] using
    tendsto_inv_fourthRoot_log_asymptoticUcbSchedule_zero

lemma tendsto_sqrt_log_schedule_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.sqrt (Real.log (asymptoticUcbSchedule n)) /
          Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hprod := tendsto_log_asymptoticUcbSchedule_div_log_nat_one.mul
    tendsto_inv_sqrt_log_asymptoticUcbSchedule_zero
  have hprod' :
      Tendsto
        (fun n : ℕ ↦
          (Real.log (asymptoticUcbSchedule n) / Real.log (n : ℝ)) *
            (Real.sqrt (Real.log (asymptoticUcbSchedule n)))⁻¹)
        atTop (𝓝 0) := by simpa using hprod
  refine hprod'.congr' ?_
  filter_upwards [eventually_pos_log_asymptoticUcbSchedule,
    tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hL hell
  have hsqrt : 0 < Real.sqrt (Real.log (asymptoticUcbSchedule n)) :=
    Real.sqrt_pos.2 hL
  rw [div_eq_mul_inv, div_eq_mul_inv]
  field_simp [ne_of_gt hsqrt, ne_of_gt hell]
  rw [Real.sq_sqrt hL.le]

lemma tendsto_sqrt_pi_log_schedule_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) /
          Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hprod := tendsto_sqrt_pi_log_schedule_div_log_schedule_zero.mul
    tendsto_log_asymptoticUcbSchedule_div_log_nat_one
  have hprod' :
      Tendsto
        (fun n : ℕ ↦
          (Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) /
            Real.log (asymptoticUcbSchedule n)) *
              (Real.log (asymptoticUcbSchedule n) / Real.log (n : ℝ)))
        atTop (𝓝 0) := by simpa using hprod
  refine hprod'.congr' ?_
  filter_upwards [eventually_pos_log_asymptoticUcbSchedule,
    tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hL hell
  field_simp [ne_of_gt hL, ne_of_gt hell]

lemma tendsto_log_schedule_correction_ratio_one :
    Tendsto
      (fun n : ℕ ↦
        (Real.log (asymptoticUcbSchedule n) +
          Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1) /
            Real.log (n : ℝ))
      atTop (𝓝 1) := by
  have hsum :=
    (tendsto_log_asymptoticUcbSchedule_div_log_nat_one.add
      tendsto_sqrt_pi_log_schedule_div_log_nat_zero).add
        tendsto_inv_log_nat_zero
  simpa [add_div, one_div] using hsum

lemma tendsto_epsilon_reciprocal_sq_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        5 / asymptoticUcbEpsilon n ^ 2 / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hmul := (tendsto_const_nhds (x := (5 : ℝ))).mul
    tendsto_sqrt_log_schedule_div_log_nat_zero
  have hmul' :
      Tendsto
        (fun n : ℕ ↦
          5 * (Real.sqrt (Real.log (asymptoticUcbSchedule n)) /
            Real.log (n : ℝ)))
        atTop (𝓝 0) := by simpa using hmul
  refine hmul'.congr' ?_
  filter_upwards [eventually_pos_log_asymptoticUcbSchedule,
    tendsto_log_nat_atTop.eventually_gt_atTop 0] with n hL hell
  have hsqrtL : 0 < Real.sqrt (Real.log (asymptoticUcbSchedule n)) :=
    Real.sqrt_pos.2 hL
  have hfourth :
      0 < Real.sqrt (Real.sqrt (Real.log (asymptoticUcbSchedule n))) :=
    Real.sqrt_pos.2 hsqrtL
  rw [asymptoticUcbEpsilon]
  field_simp [ne_of_gt hfourth, ne_of_gt hell]
  rw [Real.sq_sqrt hsqrtL.le]

lemma tendsto_one_add_epsilon_term_div_log_nat_zero :
    Tendsto
      (fun n : ℕ ↦
        (1 + 5 / asymptoticUcbEpsilon n ^ 2) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hsum := tendsto_inv_log_nat_zero.add
    tendsto_epsilon_reciprocal_sq_div_log_nat_zero
  simpa [add_div, one_div] using hsum

lemma tendsto_gap_coefficient {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun n : ℕ ↦ 2 / (δ - asymptoticUcbEpsilon n) ^ 2)
      atTop (𝓝 (2 / δ ^ 2)) := by
  have hsub :
      Tendsto (fun n : ℕ ↦ δ - asymptoticUcbEpsilon n)
        atTop (𝓝 δ) := by
    simpa using tendsto_const_nhds.sub tendsto_asymptoticUcbEpsilon_zero
  have hinv := (hsub.pow 2).inv₀ (pow_ne_zero 2 (ne_of_gt hδ))
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul hinv

lemma tendsto_arm_finite_bound_div_log_nat {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun n : ℕ ↦
        δ *
          (1 + 5 / asymptoticUcbEpsilon n ^ 2 +
            2 / (δ - asymptoticUcbEpsilon n) ^ 2 *
              (Real.log (asymptoticUcbSchedule n) +
                Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1)) /
          Real.log (n : ℝ))
      atTop (𝓝 (2 / δ)) := by
  have hlarge := (tendsto_gap_coefficient hδ).mul
    tendsto_log_schedule_correction_ratio_one
  have hinside := tendsto_one_add_epsilon_term_div_log_nat_zero.add hlarge
  have hscaled := (tendsto_const_nhds (x := δ)).mul hinside
  convert hscaled using 1
  · funext n
    ring
  · congr 1
    field_simp [ne_of_gt hδ]
    ring

lemma tendsto_finite_sum_bound_div_log_nat {k : ℕ} (Δ : Fin k → ℝ) :
    Tendsto
      (fun n : ℕ ↦
        (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
          Δ i *
            (1 + 5 / asymptoticUcbEpsilon n ^ 2 +
              2 / (Δ i - asymptoticUcbEpsilon n) ^ 2 *
                (Real.log (asymptoticUcbSchedule n) +
                  Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1))) /
          Real.log (n : ℝ))
      atTop
      (𝓝 (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i), 2 / Δ i)) := by
  simpa [Finset.sum_div] using
    tendsto_finset_sum (Finset.univ.filter (fun i ↦ 0 < Δ i))
      (fun i hi ↦ tendsto_arm_finite_bound_div_log_nat
        (Finset.mem_filter.1 hi).2)

end BanditAlgorithm

open BanditAlgorithm

theorem solution {k : ℕ}
    (R : ℕ → ℝ) (Δ : Fin k → ℝ)
    (hR : ∀ (n : ℕ) (ε : Fin k → ℝ),
      (∀ i, 0 < Δ i → 0 < ε i ∧ ε i < Δ i) →
      R n ≤
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
          Δ i *
            (1 + 5 / (ε i) ^ 2 +
              2 / (Δ i - ε i) ^ 2 *
                (Real.log (asymptoticUcbSchedule n) +
                  Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1))) :
    atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (R n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
        ENNReal.ofReal (2 / Δ i) := by
  let B : ℕ → ℝ := fun n ↦
    (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
      Δ i *
        (1 + 5 / asymptoticUcbEpsilon n ^ 2 +
          2 / (Δ i - asymptoticUcbEpsilon n) ^ 2 *
            (Real.log (asymptoticUcbSchedule n) +
              Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1))) /
      Real.log (n : ℝ)
  have hBreal :
      Tendsto B atTop
        (𝓝 (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i), 2 / Δ i)) := by
    simpa [B] using tendsto_finite_sum_bound_div_log_nat Δ
  have hBenn := ENNReal.tendsto_ofReal hBreal
  have hpointwise :
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (R n / Real.log n) ≤ ENNReal.ofReal (B n) := by
    filter_upwards
      [eventually_finite_bound_at_asymptoticUcbEpsilon R Δ hR,
        tendsto_log_nat_atTop.eventually_gt_atTop 0]
      with n hn hlog
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right hn hlog.le
  calc
    atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (R n / Real.log n)) ≤
        atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (B n)) :=
      limsup_le_limsup hpointwise
    _ = ENNReal.ofReal
        (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i), 2 / Δ i) :=
      hBenn.limsup_eq
    _ = ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < Δ i),
        ENNReal.ofReal (2 / Δ i) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact div_nonneg (by norm_num) (Finset.mem_filter.1 hi).2.le
