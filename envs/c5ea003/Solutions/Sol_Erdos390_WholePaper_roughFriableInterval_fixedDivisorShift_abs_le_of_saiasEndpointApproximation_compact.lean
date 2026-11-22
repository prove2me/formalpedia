-- Prove2me | solution 1 for Erdos390.WholePaper.roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:48:52.633511+00:00
-- url     : https://prove2.me/submissions/badc1b8f-b5f7-4537-b3fa-9e086d827de6

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_009
import Theorems.Thm_Erdos390_WholePaper_roughFriableContinuousFixedDivisorDefect_sub_abs_le_compact
import Theorems.Thm_Erdos390_WholePaper_roughSaiasDickmanCorrection_difference_abs_le_compact



section
theorem Erdos390.WholePaper.roughSaiasDickmanCorrection_difference_abs_le : Erdos390.RemainingAnalyticGoal008_026 := @Erdos390.WholePaper.roughSaiasDickmanCorrection_difference_abs_le_compact
end
section
theorem Erdos390.WholePaper.roughFriableContinuousFixedDivisorDefect_sub_abs_le : Erdos390.RemainingAnalyticGoal008_020 := @Erdos390.WholePaper.roughFriableContinuousFixedDivisorDefect_sub_abs_le_compact
end
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



/-! ## The closed fixed-head endpoint theorem -/



/-! ## Literal two-piece physical blocks -/





/-! ## Complete head Mobius closure at the available scale -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughBalancedFriableResidualReduction -/
section


/-!
# Residual cancellation in the balanced four-endpoint friable block

The closed de Bruijn theorem controls the endpoint residual

`R(X,y) = Psi(X,y) - X * rho(log X / log y)`

by `O(X / log y)`.  Applying that estimate independently at four
endpoints loses one logarithm.  This file avoids that lossy triangle
inequality.  It proves that the literal four-endpoint residual is exactly
two *short residual increments* plus one broad increment whose coefficient
already contains `1/L`.

It also records the exact reverse Buchstab recurrence for `R`, using one
common prime interval for both endpoints.  The remaining missing analytic
input is thereby reduced to a local regularity inequality for `R`; it is
strictly an estimate for the genuine friable counting function and contains
no selector, row, rounding, or feasibility conclusion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The genuine endpoint residual -/









/-- The count is exactly its Dickman main term plus the genuine residual. -/
theorem roughFriableCount_eq_main_add_residual (X y : ℕ) :
    (FriableAsymptotic.friableCount X y : ℝ) =
      roughFriableDickmanMain X y + roughFriableResidual X y := by
  unfold roughFriableResidual
  ring





/-! ## Exact reverse Buchstab recurrence for the residual -/













/-! ## Verified regularity of the Dickman main term -/







/-! ## The literal four-endpoint residual collapse -/











/-! ## The one remaining analytic inequality -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasNormalization -/
section


/-!
# The finite de Bruijn--Saias normal form on the five Dickman faces

Section 8.5 of the paper uses the integration-by-parts identity

`Lambda(z,y) = z * G_y(log z / log y) - fract z`,

where

`G_y(u) = rho(u) - integral rho'(u-v) * fract(y^v) * y^(-v) dv`.

This file formalizes the finite normal form, its exact initial face, the
compact bounded-variation datum behind the asserted Lipschitz estimate, and
the exact way in which this normalization enters the already isolated rough
prime-transition ledger.

The cited Hildebrand--Tenenbaum--Saias estimate for `Psi - Lambda` is not
proved in the paper.  Accordingly, no theorem below declares that estimate
as an axiom.  Its precise endpoint-shaped consequence is exposed as a `Prop`
which can be passed to a reduction theorem.  In particular, the endpoint
error remains proportional to `A+B`, not to the short gap `B-A`.
-/

open scoped BigOperators Interval ENNReal

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The finite `G_y` normal form -/









































/-! ## The bounded-variation datum and compact Lipschitz reduction -/





















/-! ## The explicit `1 / log y` normalization correction -/











/-! ## Exact connection to the genuine friable residual -/











/-- Exact decomposition of the already-defined genuine residual. -/
theorem roughFriableResidual_eq_saiasError_add_correction (X y : ℕ) :
    roughFriableResidual X y =
      roughSaiasEndpointError X y + roughSaiasDickmanCorrection X y := by
  unfold roughFriableResidual roughFriableDickmanMain
    roughSaiasEndpointError roughSaiasNaturalMain
    roughSaiasDickmanCorrection
  ring



/-- Exact finite-difference decomposition of the genuine friable residual. -/
theorem roughFriableResidual_difference_eq_saias
    (A B y : ℕ) :
    roughFriableResidual B y - roughFriableResidual A y =
      (roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y) := by
  rw [roughFriableResidual_eq_saiasError_add_correction,
    roughFriableResidual_eq_saiasError_add_correction]
  ring







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasWeightedTransition -/
section


/-!
# Paper-scale weighted Saias transitions

The local residual predicate used by the method-of-steps development asks
for a short-interval estimate at every pair of natural endpoints.  That is
stronger than the Hildebrand--Tenenbaum--Saias input used in the paper.
The paper only needs one fixed four-endpoint block.  In that block the two
short increments have coefficients `1` and `delta * alpha`, while the broad
half-scale increment already has the coefficient `delta * beta / L`.

This file records that weaker and directly usable interface.  The endpoint
HT--Saias envelope contributes

`eta(y) * (A + B) + 5 * (B - A) / log y`

to a specified pair.  We retain those three contributions with their exact
block coefficients and close them to the existing
`roughPhysicalFriableCombination`.  No universal adjacent-pair regularity,
prime-transition predicate, selector conclusion, or new axiom is assumed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## A transition budget for one specified pair -/



/-- HT--Saias endpoint approximation gives the desired residual increment
bound at any *specified* ordered pair.  Unlike the prime-transition ledger
form, this statement also covers the initial face `B <= y`; no reverse
Buchstab recurrence or universal local predicate is needed. -/
theorem roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hA : 0 < A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableResidual B y - roughFriableResidual A y| ≤
      roughSaiasPairTransitionBudget eta A B y := by
  have hB : 0 < B := hA.trans_le hAB
  have hlogA : Real.log (A : ℝ) ≤
      5 * Real.log (y : ℝ) := by
    have hABlog : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
      Real.log_le_log (by exact_mod_cast hA) (by exact_mod_cast hAB)
    exact hABlog.trans hlogB
  have herrorA : |roughSaiasEndpointError A y| ≤ eta y * (A : ℝ) :=
    happrox hY hy2 hA hlogA
  have herrorB : |roughSaiasEndpointError B y| ≤ eta y * (B : ℝ) :=
    happrox hY hy2 hB hlogB
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hB5 : FriableAsymptotic.dickmanU B y ≤ 5 := by
    dsimp [FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogy).2 hlogB
  have hcorrection := roughSaiasDickmanCorrection_difference_abs_le
    hBV hA hAB hy2 hB5
  rw [roughFriableResidual_difference_eq_saias]
  calc
    |(roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y)| ≤
      |roughSaiasEndpointError B y - roughSaiasEndpointError A y| +
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y| := abs_add_le _ _
    _ ≤ (|roughSaiasEndpointError B y| +
          |roughSaiasEndpointError A y|) +
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y| := by
      exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ (eta y * (B : ℝ) + eta y * (A : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
      add_le_add (add_le_add herrorB herrorA) hcorrection
    _ = roughSaiasPairTransitionBudget eta A B y := by
      unfold roughSaiasPairTransitionBudget
      ring

/-! ## The literal weighted four-endpoint block -/









/-! ## Paper-scale absorption and selector-facing closure -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpFixedHeadIntervalShift -/
section


/-!
# Sharp fixed-head interval shifts

The endpointwise fixed-head estimate loses one logarithm because it takes
absolute values before subtracting the two endpoints of an interval.  This
file retains that subtraction.  The Dickman main terms are first compared
at the interval level; the two residual increments are then bounded by the
already-proved sharp Saias endpoint approximation.

No new analytic predicate is introduced.  In particular, the only
approximation used below is
`roughSaiasSharpEndpointApproximationUpToFive`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The interval-level Dickman cancellation -/



/-- Flooring `X/d` costs at most three in the translated continuous
Dickman main term.  This is the floor part of
`roughFriableMain_fixedDivisorShift`, recorded separately so that the
translation defects at two endpoints can be subtracted before taking
absolute values. -/
theorem roughFriableMain_quotientFloor_stability
    {X y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdX : d ≤ X)
    (hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableDickmanMain (X / d) y -
        (X : ℝ) / (d : ℝ) *
          rho (FriableAsymptotic.dickmanU X y -
            Real.log (d : ℝ) / Real.log (y : ℝ))| ≤ 3 := by
  have hX : 0 < X := hd.trans_le hdX
  have hA : 1 ≤ X / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    simpa using hdX
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hXReal : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hyReal : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  let r : ℝ := (X : ℝ) / (d : ℝ)
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
  simpa only [roughFriableDickmanMain,
    FriableAsymptotic.dickmanU, hcoordinate, r] using hfloor



/-- After the two quotient floors are restored, the interval Dickman shift
has the desired length-over-log scale, plus the two absolute floor
constants. -/
theorem roughFriableDickmanMain_interval_fixedDivisorShift_abs_le
    {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)| ≤
      6 + ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) := by
  have hdB : d ≤ B := hdA.trans hAB
  let floorError : ℕ → ℝ := fun X ↦
    roughFriableDickmanMain (X / d) y -
      (X : ℝ) / (d : ℝ) *
        rho (FriableAsymptotic.dickmanU X y -
          Real.log (d : ℝ) / Real.log (y : ℝ))
  have hfloorA : |floorError A| ≤ 3 := by
    simpa only [floorError] using
      roughFriableMain_quotientFloor_stability hy hd hdA
        (by
          have hA : 0 < A := hd.trans_le hdA
          have hlogAB : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
            Real.log_le_log (by exact_mod_cast hA)
              (by exact_mod_cast hAB)
          exact hlogAB.trans hlogB)
  have hfloorB : |floorError B| ≤ 3 := by
    simpa only [floorError] using
      roughFriableMain_quotientFloor_stability hy hd hdB hlogB
  have hcontinuous :=
    roughFriableContinuousFixedDivisorDefect_sub_abs_le
      hy hd hdA hAB hlogB
  have hrearrange :
      (roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ) =
      (floorError B - floorError A) +
        (roughFriableContinuousFixedDivisorDefect B y d -
          roughFriableContinuousFixedDivisorDefect A y d) := by
    dsimp [floorError, roughFriableContinuousFixedDivisorDefect,
      roughFriableDickmanMain]
    ring
  rw [hrearrange]
  calc
    |(floorError B - floorError A) +
        (roughFriableContinuousFixedDivisorDefect B y d -
          roughFriableContinuousFixedDivisorDefect A y d)| ≤
      (|floorError B| + |floorError A|) +
        |roughFriableContinuousFixedDivisorDefect B y d -
          roughFriableContinuousFixedDivisorDefect A y d| := by
            calc
              _ ≤ |floorError B - floorError A| +
                  |roughFriableContinuousFixedDivisorDefect B y d -
                    roughFriableContinuousFixedDivisorDefect A y d| :=
                abs_add_le _ _
              _ ≤ (|floorError B| + |floorError A|) +
                  |roughFriableContinuousFixedDivisorDefect B y d -
                    roughFriableContinuousFixedDivisorDefect A y d| :=
                add_le_add (abs_sub _ _) le_rfl
    _ ≤ (3 + 3) +
        ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 2) /
            ((d : ℝ) * Real.log (y : ℝ)) :=
      add_le_add (add_le_add hfloorB hfloorA) hcontinuous
    _ = 6 + ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) := by ring

/-! ## Adding the two residual increments -/



/-- A Saias endpoint approximation controls the genuine friable interval
shift at the cancellation-preserving scale.  This theorem does not take
absolute values of four endpoint shifts: it takes absolute values only
after forming the divided and undivided residual increments. -/
theorem roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y d : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy : 2 ≤ y)
    (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((FriableAsymptotic.friableCount (B / d) y : ℝ) -
          (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
        ((FriableAsymptotic.friableCount B y : ℝ) -
          (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ)| ≤
      roughSaiasIntervalFixedDivisorShiftBudget eta A B y d := by
  have hA : 0 < A := hd.trans_le hdA
  have hB : 0 < B := hA.trans_le hAB
  have hdB : d ≤ B := hdA.trans hAB
  have hqA : 0 < A / d := Nat.div_pos hdA hd
  have hqB : 0 < B / d := Nat.div_pos hdB hd
  have hqAB : A / d ≤ B / d := Nat.div_le_div_right hAB
  have hqBlog :
      Real.log ((B / d : ℕ) : ℝ) ≤
        5 * Real.log (y : ℝ) := by
    have hmono :
        Real.log ((B / d : ℕ) : ℝ) ≤ Real.log (B : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hqB
      · exact_mod_cast Nat.div_le_self B d
    exact hmono.trans hlogB
  have hmain :=
    roughFriableDickmanMain_interval_fixedDivisorShift_abs_le
      hy hd hdA hAB hlogB
  have hsmall :=
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy hqA hqAB hqBlog
  have hlarge :=
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy hA hAB hlogB
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlarge' :
      |(roughFriableResidual B y - roughFriableResidual A y) /
          (d : ℝ)| ≤
        roughSaiasPairTransitionBudget eta A B y / (d : ℝ) := by
    rw [abs_div, abs_of_pos hdReal]
    exact (div_le_div_iff_of_pos_right hdReal).2 hlarge
  have hrearrange :
      ((FriableAsymptotic.friableCount (B / d) y : ℝ) -
          (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
        ((FriableAsymptotic.friableCount B y : ℝ) -
          (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ) =
      ((roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)) +
      (roughFriableResidual (B / d) y -
        roughFriableResidual (A / d) y) -
      (roughFriableResidual B y -
        roughFriableResidual A y) / (d : ℝ) := by
    rw [roughFriableCount_eq_main_add_residual (B / d) y,
      roughFriableCount_eq_main_add_residual (A / d) y,
      roughFriableCount_eq_main_add_residual B y,
      roughFriableCount_eq_main_add_residual A y]
    ring
  rw [hrearrange]
  calc
    |((roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)) +
      (roughFriableResidual (B / d) y -
        roughFriableResidual (A / d) y) -
      (roughFriableResidual B y -
        roughFriableResidual A y) / (d : ℝ)| ≤
      |(roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)| +
      |roughFriableResidual (B / d) y -
        roughFriableResidual (A / d) y| +
      |(roughFriableResidual B y -
        roughFriableResidual A y) / (d : ℝ)| := by
          calc
            _ ≤
              |((roughFriableDickmanMain (B / d) y -
                    roughFriableDickmanMain (A / d) y) -
                  (roughFriableDickmanMain B y -
                    roughFriableDickmanMain A y) / (d : ℝ)) +
                (roughFriableResidual (B / d) y -
                  roughFriableResidual (A / d) y)| +
              |(roughFriableResidual B y -
                roughFriableResidual A y) / (d : ℝ)| :=
              abs_sub _ _
            _ ≤
              (|(roughFriableDickmanMain (B / d) y -
                    roughFriableDickmanMain (A / d) y) -
                  (roughFriableDickmanMain B y -
                    roughFriableDickmanMain A y) / (d : ℝ)| +
                |roughFriableResidual (B / d) y -
                  roughFriableResidual (A / d) y|) +
              |(roughFriableResidual B y -
                roughFriableResidual A y) / (d : ℝ)| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ = _ := by ring
    _ ≤
      (6 + ((B - A : ℕ) : ℝ) *
          (Real.log (d : ℝ) + 2) /
            ((d : ℝ) * Real.log (y : ℝ))) +
      roughSaiasPairTransitionBudget eta (A / d) (B / d) y +
      roughSaiasPairTransitionBudget eta A B y / (d : ℝ) :=
        add_le_add (add_le_add hmain hsmall) hlarge'
    _ = roughSaiasIntervalFixedDivisorShiftBudget eta A B y d := by
      rfl

/-! ## The closed inverse-log-square specialization -/







/-! ## Physical blocks and the finite head -/

















end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_021 := by
  exact @Erdos390.WholePaper.roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation
