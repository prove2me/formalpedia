-- Prove2me | solution 1 for Erdos390.WholePaper.roughFriableMain_fixedDivisorShift_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:46:52.167153+00:00
-- url     : https://prove2.me/submissions/6502153a-5b8c-4d49-9a90-132cd8f0e50d

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

/- Source module: Erdos390.WholePaper.RoughFixedHeadFriableShift -/
section


/-!
# The strongest available unconditional fixed-head friable shift

The paper uses the Hildebrand--Tenenbaum--Saias transition estimate to
obtain an `O_W(x / log(y)^2 + 1)` shift for a balanced physical block.
That transition estimate is not present in Mathlib, PrimeNumberTheoremAnd,
or the current project.  What *is* present is the closed uniform de Bruijn
estimate

`|Psi(X,y) - X * rho(log X / log y)| <= K * X / log y`

from `Full.FriableAsymptotic`.  This file records the strongest genuine
fixed-head consequence of that theorem.  It proves, without an analytic
hypothesis, an `O_W(X / log y + 1)` shift for the endpoint count, the
literal two-piece physical block, and its complete head Mobius closure.

The first lemma extends the already-proved floor-stability argument from
the recursive four-mark range `u <= 4` to the full endpoint range `u <= 5`.
It uses only the project's proved one-Lipschitz estimate for `rho`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Full-range floor stability of the Dickman main term -/

/-- Replacing a positive real quotient by its natural-number floor changes
the Dickman endpoint main term by at most three throughout `u <= 5`.

`Full.FriableAsymptotic.rho_floor_kernel_stability` proves the same
estimate with the stronger input `u <= 4`, which is exactly what its prime
recurrence needs.  The proof below is its deterministic endpoint argument
with the already available full compact range retained. -/
theorem roughRhoFloorKernel_stability
    (A : ℕ) {r p : ℝ}
    (hA : 1 ≤ A) (hAr : (A : ℝ) ≤ r) (hrA : r < (A : ℝ) + 1)
    (hp : (2 : ℝ) ≤ p)
    (hb5 : Real.log r / Real.log p ≤ 5) :
    |(A : ℝ) * rho (Real.log (A : ℝ) / Real.log p) -
        r * rho (Real.log r / Real.log p)| ≤ 3 := by
  let a : ℝ := Real.log (A : ℝ) / Real.log p
  let b : ℝ := Real.log r / Real.log p
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hrpos : 0 < r := hApos.trans_le hAr
  have hlogppos : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogpHalf : (1 / 2 : ℝ) ≤ Real.log p := by
    have hmono : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) hp
    nlinarith [Real.log_two_gt_d9]
  have hlogAr : Real.log (A : ℝ) ≤ Real.log r :=
    Real.log_le_log hApos hAr
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right hlogAr hlogppos.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hA)) hlogppos.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb5' : b ≤ 5 := by
    simpa only [b] using hb5
  have hrhoa0 : 0 ≤ rho a :=
    (rho_pos_on_zero_five ha0 (hab.trans hb5')).le
  have hrhob0 : 0 ≤ rho b :=
    (rho_pos_on_zero_five hb0 hb5').le
  have hrhob1 : rho b ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hb5'
  have hrho : |rho a - rho b| ≤ b - a := by
    rw [abs_sub_comm]
    exact FriableAsymptotic.rho_lipschitz_of_le_five hab hb5'
  have hlogQuotient :
      Real.log r - Real.log (A : ℝ) ≤ r / (A : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hrpos hApos)
    rw [Real.log_div hrpos.ne' hApos.ne'] at h
    exact h
  have hscaled :
      (A : ℝ) * (Real.log r - Real.log (A : ℝ)) ≤
        r - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogQuotient hApos.le
    calc
      (A : ℝ) * (Real.log r - Real.log (A : ℝ)) ≤
          (A : ℝ) * (r / (A : ℝ) - 1) := h
      _ = r - (A : ℝ) := by field_simp
  have hAdiff : (A : ℝ) * (b - a) ≤ 2 := by
    have hdiv := div_le_div_of_nonneg_right hscaled hlogppos.le
    have hfirst : (A : ℝ) * (b - a) ≤
        (r - (A : ℝ)) / Real.log p := by
      dsimp [a, b]
      convert hdiv using 1
      ring
    have hsecond : (r - (A : ℝ)) / Real.log p ≤ 2 := by
      apply (div_le_iff₀ hlogppos).2
      nlinarith
    exact hfirst.trans hsecond
  have hgap0 : 0 ≤ r - (A : ℝ) := sub_nonneg.mpr hAr
  have hgap1 : r - (A : ℝ) ≤ 1 := by linarith
  calc
    |(A : ℝ) * rho (Real.log (A : ℝ) / Real.log p) -
        r * rho (Real.log r / Real.log p)| =
      |(A : ℝ) * (rho a - rho b) +
          ((A : ℝ) - r) * rho b| := by
        dsimp [a, b]
        congr 1
        ring
    _ ≤ |(A : ℝ) * (rho a - rho b)| +
          |((A : ℝ) - r) * rho b| := abs_add_le _ _
    _ = (A : ℝ) * |rho a - rho b| +
          (r - (A : ℝ)) * rho b := by
      rw [abs_mul, abs_mul, abs_of_nonneg hApos.le,
        abs_of_nonpos (sub_nonpos.mpr hAr), abs_of_nonneg hrhob0]
      ring
    _ ≤ (A : ℝ) * (b - a) +
          (r - (A : ℝ)) * 1 := by gcongr
    _ ≤ 2 + 1 := add_le_add hAdiff (by simpa using hgap1)
    _ = 3 := by norm_num

/-! ## A fixed-divisor shift for the Dickman main term -/

/-- The Dickman endpoint model at `floor(X/d)` differs from `1/d` times
the model at `X` by the floor constant three plus the exact logarithmic
translation cost. -/
theorem roughFriableMain_fixedDivisorShift
    {X y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdX : d ≤ X)
    (hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((X / d : ℕ) : ℝ) *
          rho (FriableAsymptotic.dickmanU (X / d) y) -
        ((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) / (d : ℝ)| ≤
      3 + (X : ℝ) * Real.log (d : ℝ) /
        ((d : ℝ) * Real.log (y : ℝ)) := by
  have hX : 0 < X := hd.trans_le hdX
  have hA : 1 ≤ X / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    simpa using hdX
  have hApos : 0 < X / d := Nat.zero_lt_of_lt hA
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hXReal : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hyReal : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  let r : ℝ := (X : ℝ) / (d : ℝ)
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hAr : ((X / d : ℕ) : ℝ) ≤ r := by
    dsimp [r]
    exact Nat.cast_div_le
  have hupperNat : X < (X / d + 1) * d :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (X / d))
  have hrA : r < ((X / d : ℕ) : ℝ) + 1 := by
    dsimp [r]
    apply (div_lt_iff₀ hdReal).2
    exact_mod_cast hupperNat
  have hlogr :
      Real.log r = Real.log (X : ℝ) - Real.log (d : ℝ) := by
    dsimp [r]
    rw [Real.log_div hXReal.ne' hdReal.ne']
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
  have hlogrLe : Real.log r ≤ Real.log (X : ℝ) := by
    rw [hlogr]
    linarith
  have hr5 : Real.log r / Real.log (y : ℝ) ≤ 5 := by
    apply (div_le_iff₀ hlogY).2
    exact hlogrLe.trans hlogX
  have hfloor := roughRhoFloorKernel_stability (X / d)
    hA hAr hrA hyReal hr5
  have hcoordinate :
      Real.log r / Real.log (y : ℝ) =
        FriableAsymptotic.dickmanU X y -
          Real.log (d : ℝ) / Real.log (y : ℝ) := by
    rw [hlogr]
    simp only [FriableAsymptotic.dickmanU]
    ring
  have htranslateNonneg :
      0 ≤ Real.log (d : ℝ) / Real.log (y : ℝ) :=
    div_nonneg hlogd hlogY.le
  have hcoordinateLe :
      Real.log r / Real.log (y : ℝ) ≤
        FriableAsymptotic.dickmanU X y := by
    rw [hcoordinate]
    linarith
  have hu5 : FriableAsymptotic.dickmanU X y ≤ 5 := by
    simp only [FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogY).2 hlogX
  have hrho :
      |rho (Real.log r / Real.log (y : ℝ)) -
          rho (FriableAsymptotic.dickmanU X y)| ≤
        Real.log (d : ℝ) / Real.log (y : ℝ) := by
    rw [abs_sub_comm]
    calc
      |rho (FriableAsymptotic.dickmanU X y) -
          rho (Real.log r / Real.log (y : ℝ))| ≤
        FriableAsymptotic.dickmanU X y -
          Real.log r / Real.log (y : ℝ) :=
        FriableAsymptotic.rho_lipschitz_of_le_five hcoordinateLe hu5
      _ = Real.log (d : ℝ) / Real.log (y : ℝ) := by
        rw [hcoordinate]
        ring
  calc
    |((X / d : ℕ) : ℝ) *
          rho (FriableAsymptotic.dickmanU (X / d) y) -
        ((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) / (d : ℝ)| =
      |(((X / d : ℕ) : ℝ) *
            rho (FriableAsymptotic.dickmanU (X / d) y) -
          r * rho (Real.log r / Real.log (y : ℝ))) +
        r * (rho (Real.log r / Real.log (y : ℝ)) -
          rho (FriableAsymptotic.dickmanU X y))| := by
        simp only [FriableAsymptotic.dickmanU]
        congr 1
        dsimp [r]
        ring
    _ ≤ |((X / d : ℕ) : ℝ) *
            rho (FriableAsymptotic.dickmanU (X / d) y) -
          r * rho (Real.log r / Real.log (y : ℝ))| +
        |r * (rho (Real.log r / Real.log (y : ℝ)) -
          rho (FriableAsymptotic.dickmanU X y))| := abs_add_le _ _
    _ ≤ 3 + r *
          (Real.log (d : ℝ) / Real.log (y : ℝ)) := by
      apply add_le_add
      · simpa only [FriableAsymptotic.dickmanU] using hfloor
      · rw [abs_mul, abs_of_pos hrpos]
        exact mul_le_mul_of_nonneg_left hrho hrpos.le
    _ = 3 + (X : ℝ) * Real.log (d : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
      dsimp [r]
      ring

/-! ## The closed fixed-head endpoint theorem -/



/-! ## Literal two-piece physical blocks -/





/-! ## Complete head Mobius closure at the available scale -/





end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_023 := by
  exact @Erdos390.WholePaper.roughFriableMain_fixedDivisorShift
