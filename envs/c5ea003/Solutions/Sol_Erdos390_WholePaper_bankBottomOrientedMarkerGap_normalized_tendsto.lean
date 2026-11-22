-- Prove2me | solution 1 for Erdos390.WholePaper.bankBottomOrientedMarkerGap_normalized_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:01:37.879478+00:00
-- url     : https://prove2.me/submissions/de44285c-527c-483f-8ba2-3f37198a282f

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

/- Source module: Erdos390.WholePaper.UpperScale -/
section


/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section





/-- The elementary logarithmic comparison `log n / n → 0`, made public
for later upper-bound estimates. -/
theorem log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

/-- The second-order scale `n / log n` diverges to infinity. -/
theorem secondOrderScale_tendsto_atTop :
    Tendsto secondOrderScale atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop,
        0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright :
      Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨log_natCast_div_natCast_tendsto_zero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
      secondOrderScale n
    rw [secondOrderScale, inv_div]

/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

/-- Eventually the second-order scale is strictly positive. -/
theorem eventually_secondOrderScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact secondOrderScale_pos hn







/-- Ceiling changes `c n/log n` only by a negligible relative error. -/
theorem upperTailLength_normalized_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailLength c n : ℝ) / secondOrderScale n)
      atTop (nhds c) := by
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
      secondOrderScale_tendsto_atTop





/-- Every upper endpoint lies weakly above `2n`. -/
theorem two_mul_le_upperEndpoint (n h : ℕ) :
    2 * n ≤ upperEndpoint n h := by
  simp only [upperEndpoint, Nat.le_add_right]

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomMarkerPoolScale -/
section


/-!
# Prime-counting scales for bottom marker pools

The bottom intervals have length of order `n / log n`, while their prime
cardinality has order `n / log n ^ 2`.  Consequently their cardinality
divided by `secondOrderScale n = n / log n` tends to zero, not to a positive
constant.  This file records that coarse-scale fact and then applies the
audited `theta`-difference squeeze to obtain the positive constants on the
finer scale `secondOrderScale n / log n`.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section





















theorem bankBottomMarkerDenominator_pos (move : BankBottomMove) :
    0 < bankBottomMarkerDenominator move := by
  cases move <;> norm_num [bankBottomMarkerDenominator]







theorem bankBottomOrientedMarkerLower_le_upper
    {n M : ℕ} (hM : 2 * n ≤ M) (pool : BankBottomOrientationPool) :
    bankBottomOrientedMarkerLower n M pool ≤
      bankBottomOrientedMarkerUpper n M pool := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · exact bankBottomMarkerLower_le_cut n M move
  · exact bankBottomOrientationCut_le_upper hM move

private theorem natDiv_scale_normalized_tendsto
    {m : ℕ → ℕ} {scale : ℕ → ℝ} {a : ℝ}
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / scale n)
      atTop (nhds a))
    (hscale : Tendsto scale atTop atTop)
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ ↦ ((m n / d : ℕ) : ℝ) / scale n)
      atTop (nhds (a / (d : ℝ))) := by
  have hmain :
      Tendsto
        (fun n : ℕ ↦ ((m n : ℝ) / scale n) / (d : ℝ))
        atTop (nhds (a / (d : ℝ))) :=
    hm.div_const (d : ℝ)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / scale n)
      atTop (nhds 0) := by
    simpa only [one_div] using hscale.inv_tendsto_atTop
  have hlower : Tendsto
      (fun n : ℕ ↦
        ((m n : ℝ) / scale n) / (d : ℝ) - 1 / scale n)
      atTop (nhds (a / (d : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hmain
  · filter_upwards [hscale.eventually (eventually_gt_atTop 0)] with n hn
    have hfloor :
        (m n : ℝ) / (d : ℝ) < ((m n / d : ℕ) : ℝ) + 1 := by
      simpa only [Nat.floor_div_eq_div] using
        (Nat.lt_floor_add_one ((m n : ℝ) / (d : ℝ)))
    have hbase :
        (m n : ℝ) / (d : ℝ) - 1 ≤ ((m n / d : ℕ) : ℝ) := by
      linarith
    calc
      ((m n : ℝ) / scale n) / (d : ℝ) - 1 / scale n =
          ((m n : ℝ) / (d : ℝ) - 1) / scale n := by
            have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
            field_simp
      _ ≤ ((m n / d : ℕ) : ℝ) / scale n :=
        div_le_div_of_nonneg_right hbase hn.le
  · filter_upwards [hscale.eventually (eventually_gt_atTop 0)] with n hn
    have hcast : ((m n / d : ℕ) : ℝ) ≤ (m n : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    calc
      ((m n / d : ℕ) : ℝ) / scale n ≤
          ((m n : ℝ) / (d : ℝ)) / scale n :=
        div_le_div_of_nonneg_right hcast hn.le
      _ = ((m n : ℝ) / scale n) / (d : ℝ) := by
        have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
        field_simp

/-- The full row width differs from the tail length divided by the row
denominator by at most one integer. -/
theorem bankBottomMarkerGap_bounds
    (n h : ℕ) (move : BankBottomMove) :
    h / bankBottomMarkerDenominator move ≤
        bankBottomMarkerUpper (upperEndpoint n h) move -
          bankBottomMarkerLower n move ∧
      bankBottomMarkerUpper (upperEndpoint n h) move -
          bankBottomMarkerLower n move ≤
        h / bankBottomMarkerDenominator move + 1 := by
  cases move <;>
    simp only [bankBottomMarkerDenominator, bankBottomMarkerUpper,
      bankBottomMarkerLower, upperEndpoint] <;>
    omega

/-- Thus an unsplit row has normalized width `c / d` on the
`secondOrderScale` length scale. -/
theorem bankBottomMarkerGap_normalized_tendsto
    {c : ℝ} (hc : 0 < c) (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move : ℝ) -
            (bankBottomMarkerLower n move : ℝ)) /
          secondOrderScale n)
      atTop (nhds (c / (bankBottomMarkerDenominator move : ℝ))) := by
  have hdiv := natDiv_scale_normalized_tendsto
    (upperTailLength_normalized_tendsto hc)
    secondOrderScale_tendsto_atTop
    (bankBottomMarkerDenominator move)
    (bankBottomMarkerDenominator_pos move)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / secondOrderScale n)
      atTop (nhds 0) := by
    simpa only [one_div] using secondOrderScale_tendsto_atTop.inv_tendsto_atTop
  have hupper : Tendsto
      (fun n : ℕ ↦
        ((upperTailLength c n / bankBottomMarkerDenominator move : ℕ) : ℝ) /
            secondOrderScale n + 1 / secondOrderScale n)
      atTop (nhds (c / (bankBottomMarkerDenominator move : ℝ))) := by
    simpa only [add_zero] using hdiv.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hdiv hupper
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hrow := bankBottomMarkerLower_le_upper
      (two_mul_le_upperEndpoint n (upperTailLength c n)) move
    have hbounds := bankBottomMarkerGap_bounds
      n (upperTailLength c n) move
    rw [← Nat.cast_sub hrow]
    apply div_le_div_of_nonneg_right _ hscale.le
    exact_mod_cast hbounds.1
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hrow := bankBottomMarkerLower_le_upper
      (two_mul_le_upperEndpoint n (upperTailLength c n)) move
    have hbounds := bankBottomMarkerGap_bounds
      n (upperTailLength c n) move
    rw [← Nat.cast_sub hrow]
    have hcast :
        (bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move -
            bankBottomMarkerLower n move : ℕ) ≤
          upperTailLength c n / bankBottomMarkerDenominator move + 1 :=
      hbounds.2
    have hdivLe :
        ((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move -
            bankBottomMarkerLower n move : ℕ) : ℝ) /
              secondOrderScale n ≤
          (((upperTailLength c n /
              bankBottomMarkerDenominator move : ℕ) : ℝ) + 1) /
            secondOrderScale n := by
      apply div_le_div_of_nonneg_right _ hscale.le
      exact_mod_cast hcast
    calc
      ((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move -
            bankBottomMarkerLower n move : ℕ) : ℝ) /
          secondOrderScale n ≤
        (((upperTailLength c n /
            bankBottomMarkerDenominator move : ℕ) : ℝ) + 1) /
          secondOrderScale n := hdivLe
      _ = ((upperTailLength c n /
              bankBottomMarkerDenominator move : ℕ) : ℝ) /
            secondOrderScale n + 1 / secondOrderScale n := by ring







/-- Both integer midpoint halves lie between `floor(width/2)` and one more
than that number. -/
theorem bankBottomOrientedMarkerGap_bounds
    {n M : ℕ} (hM : 2 * n ≤ M) (pool : BankBottomOrientationPool) :
    (bankBottomMarkerUpper M pool.1 -
        bankBottomMarkerLower n pool.1) / 2 ≤
      bankBottomOrientedMarkerUpper n M pool -
        bankBottomOrientedMarkerLower n M pool ∧
    bankBottomOrientedMarkerUpper n M pool -
        bankBottomOrientedMarkerLower n M pool ≤
      (bankBottomMarkerUpper M pool.1 -
        bankBottomMarkerLower n pool.1) / 2 + 1 := by
  rcases pool with ⟨move, orientation⟩
  have hrow := bankBottomMarkerLower_le_upper hM move
  cases orientation <;>
    simp only [bankBottomOrientedMarkerLower,
      bankBottomOrientedMarkerUpper, bankBottomOrientationCut] <;>
    omega





/-- Each fixed midpoint orientation receives exactly half the row-width
constant on the `secondOrderScale` length scale. -/
theorem bankBottomOrientedMarkerGap_normalized_tendsto
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerUpper n
              (upperEndpoint n (upperTailLength c n)) pool : ℝ) -
            (bankBottomOrientedMarkerLower n
              (upperEndpoint n (upperTailLength c n)) pool : ℝ)) /
          secondOrderScale n)
      atTop (nhds (bankBottomOrientedPrimeConstant c pool)) := by
  have hrow := bankBottomMarkerGap_normalized_tendsto hc pool.1
  have hrowNat : Tendsto
      (fun n : ℕ ↦
        ((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1 : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds (c / (bankBottomMarkerDenominator pool.1 : ℝ))) := by
    apply hrow.congr'
    exact Eventually.of_forall fun n ↦ by
      dsimp only
      rw [Nat.cast_sub (bankBottomMarkerLower_le_upper
        (two_mul_le_upperEndpoint n (upperTailLength c n)) pool.1)]
  have hhalf0 := natDiv_scale_normalized_tendsto hrowNat
    secondOrderScale_tendsto_atTop 2 (by omega)
  have hhalf : Tendsto
      (fun n : ℕ ↦
        (((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds (bankBottomOrientedPrimeConstant c pool)) := by
    simpa only [bankBottomOrientedPrimeConstant, div_div, Nat.cast_ofNat,
      mul_comm] using hhalf0
  have hinv : Tendsto (fun n : ℕ ↦ 1 / secondOrderScale n)
      atTop (nhds 0) := by
    simpa only [one_div] using secondOrderScale_tendsto_atTop.inv_tendsto_atTop
  have hupper : Tendsto
      (fun n : ℕ ↦
        (((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) /
            secondOrderScale n + 1 / secondOrderScale n)
      atTop (nhds (bankBottomOrientedPrimeConstant c pool)) := by
    simpa only [add_zero] using hhalf.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hhalf hupper
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hM := two_mul_le_upperEndpoint n (upperTailLength c n)
    have hpOrder := bankBottomOrientedMarkerLower_le_upper hM pool
    have hbounds := bankBottomOrientedMarkerGap_bounds hM pool
    rw [← Nat.cast_sub hpOrder]
    apply div_le_div_of_nonneg_right _ hscale.le
    exact_mod_cast hbounds.1
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hM := two_mul_le_upperEndpoint n (upperTailLength c n)
    have hpOrder := bankBottomOrientedMarkerLower_le_upper hM pool
    have hbounds := bankBottomOrientedMarkerGap_bounds hM pool
    rw [← Nat.cast_sub hpOrder]
    have hcast :
        (bankBottomOrientedMarkerUpper n
              (upperEndpoint n (upperTailLength c n)) pool -
            bankBottomOrientedMarkerLower n
              (upperEndpoint n (upperTailLength c n)) pool : ℕ) ≤
          (bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 + 1 :=
      hbounds.2
    have hdivLe :
        ((bankBottomOrientedMarkerUpper n
              (upperEndpoint n (upperTailLength c n)) pool -
            bankBottomOrientedMarkerLower n
              (upperEndpoint n (upperTailLength c n)) pool : ℕ) : ℝ) /
              secondOrderScale n ≤
          ((((bankBottomMarkerUpper
                (upperEndpoint n (upperTailLength c n)) pool.1 -
              bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) + 1) /
            secondOrderScale n := by
      apply div_le_div_of_nonneg_right _ hscale.le
      exact_mod_cast hcast
    calc
      ((bankBottomOrientedMarkerUpper n
              (upperEndpoint n (upperTailLength c n)) pool -
            bankBottomOrientedMarkerLower n
              (upperEndpoint n (upperTailLength c n)) pool : ℕ) : ℝ) /
          secondOrderScale n ≤
        ((((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) + 1) /
          secondOrderScale n := hdivLe
      _ = (((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) /
            secondOrderScale n + 1 / secondOrderScale n := by ring













end

end Erdos390.WholePaper

end

theorem solution :
∀ {c : Real},
  LT.lt.{0} (0 : Real) c →
    ∀ (pool : Erdos390.WholePaper.BankBottomOrientationPool),
      Filter.Tendsto.{0, 0}
        (fun n =>
          HDiv.hDiv.{0, 0, 0}
            (HSub.hSub.{0, 0, 0}
              ↑(Erdos390.WholePaper.bankBottomOrientedMarkerUpper n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) pool)
              ↑(Erdos390.WholePaper.bankBottomOrientedMarkerLower n
                  (Erdos390.WholePaper.upperEndpoint n (Erdos390.WholePaper.upperTailLength c n)) pool))
            (Erdos390.WholePaper.secondOrderScale n))
        Filter.atTop.{0} (nhds.{0} (Erdos390.WholePaper.bankBottomOrientedPrimeConstant c pool)) := by
  exact @Erdos390.WholePaper.bankBottomOrientedMarkerGap_normalized_tendsto
