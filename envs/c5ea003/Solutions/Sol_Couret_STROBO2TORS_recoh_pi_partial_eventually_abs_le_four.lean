-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_pi_partial_eventually_abs_le_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:06.529424+00:00
-- url     : https://prove2.me/submissions/2a2c69ab-cbf7-43f2-a07c-0a9eba10a645

import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Theorems.Thm_Couret_STROBO2TORS_recoh_pi_partial_error
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Mathlib.Topology.Algebra.Order.Floor

set_option autoImplicit false

/-!
Existence of finite rational precision certificates for every positive error
budget.  These theorems concern the explicit error expressions checked by
the decoder.  They do not assert refinement of the Python precision-search
loop or of its JSON interface.
-/

namespace Couret.STROBO2TORS

open Filter Topology

/-- The geometric arctangent error certificate tends to zero. -/
theorem recoh_arctan_error_tendsto_zero (x : ℚ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    Tendsto (fun n : ℕ => (recohArctanError x n : ℝ)) atTop (𝓝 0) := by
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast hx₀
  have hx1 : (x : ℝ) < 1 := by exact_mod_cast hx₁
  have hsq : (x : ℝ) ^ 2 < 1 := by nlinarith
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    (sq_nonneg (x : ℝ)) hsq).const_mul (x : ℝ)).div_const (1 - (x : ℝ) ^ 2)
  simpa only [recohArctanError, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_one, mul_zero, zero_div] using h

/-- Both Machin-series tails, with their explicit coefficients, tend to zero. -/
theorem recoh_pi_error_tendsto_zero :
    Tendsto (fun n : ℕ => (recohPiError n : ℝ)) atTop (𝓝 0) := by
  have h5 := recoh_arctan_error_tendsto_zero (1 / 5) (by norm_num) (by norm_num)
  have h239 := recoh_arctan_error_tendsto_zero (1 / 239) (by norm_num) (by norm_num)
  have h := (h5.const_mul 16).add (h239.const_mul 4)
  simpa only [recohPiError, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
    mul_zero, add_zero] using h





/-- The executable bound on the rational centre of π eventually holds. -/
theorem p2m_local_recoh_pi_partial_eventually_abs_le_four :
    ∀ᶠ n : ℕ in atTop, |recohPiPartial n| ≤ 4 := by
  have h := recoh_pi_error_tendsto_zero.eventually_lt_const
    (show (0 : ℝ) < 4 - Real.pi by linarith [Real.pi_lt_four])
  filter_upwards [h] with n hn
  have herror := recoh_pi_partial_error n
  have htri : |(recohPiPartial n : ℝ)| ≤
      |(recohPiPartial n : ℝ) - Real.pi| + Real.pi := by
    calc
      _ = |((recohPiPartial n : ℝ) - Real.pi) + Real.pi| := by ring_nf
      _ ≤ |(recohPiPartial n : ℝ) - Real.pi| + |Real.pi| := abs_add_le _ _
      _ = _ := by rw [abs_of_pos Real.pi_pos]
  have hbound : |(recohPiPartial n : ℝ)| ≤ 4 := by linarith
  exact_mod_cast hbound







end Couret.STROBO2TORS


theorem solution : @Filter.Eventually.{0} Nat
  (fun n =>
    @LE.le.{0} Rat Rat.instLE (@abs.{0} Rat Rat.instLattice Rat.addGroup (Couret.STROBO2TORS.recohPiPartial n))
      (@OfNat.ofNat.{0} Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4))))
  (@Filter.atTop.{0} Nat Nat.instPreorder) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_pi_partial_eventually_abs_le_four

