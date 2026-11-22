-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalBalancedRawSignedValuationResidualBound
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:58:40.347112+00:00
-- url     : https://prove2.me/submissions/5e77e9f7-3482-43bb-a26f-6e01254af506

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
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_abs_roughCanonicalRawPrimePowerColumnResidual_le

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.Scale -/
section


/-!
# Exact scale identities

This file records the elementary identities behind the fixed choice
`y = n^(2/9)` used throughout the marked and smooth bridge.  Keeping them as
equalities avoids repeatedly treating `U = 9/2` and the four-mark cofactor
margin as informal arithmetic simplifications.
-/

open Filter Topology

namespace Erdos390.Full.Scale

open ArithmeticModel

























theorem endpointRatio_eq {n : ℕ} (hn : 0 < n) :
    endpointRatio n = L n ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      (n : ℝ) ^ (4 / 9 : ℝ) * (n : ℝ) ^ (5 / 9 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  rw [endpointRatio, y_pow_two]
  field_simp [(Real.rpow_pos_of_pos hnR (5 / 9 : ℝ)).ne', hnR.ne']
  nlinarith

/-- In particular, all `y^2 L^2 / n` endpoint errors vanish. -/
theorem tendsto_endpointRatio_zero :
    Tendsto endpointRatio atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (5 / 9 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 5 / 9)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ))
      atTop (𝓝 0) := by
    simpa [Real.rpow_natCast] using hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [L] using (endpointRatio_eq hn).symm

end Erdos390.Full.Scale

end

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

/-- The second-order scale is sublinear. -/
theorem secondOrderScale_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ secondOrderScale n / (n : ℝ))
      atTop (nhds 0) := by
  have hinvLog :
      Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ))
        atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  apply hinvLog.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [secondOrderScale]
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  have hlogNe : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp

/-- For `c > 0`, the integral tail length itself diverges. -/
theorem upperTailLength_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (upperTailLength c) atTop atTop := by
  have hscaled :
      Tendsto (fun n : ℕ ↦ c * secondOrderScale n) atTop atTop :=
    secondOrderScale_tendsto_atTop.const_mul_atTop hc
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_atTop (α := ℝ)).comp hscaled

/-- For `c > 0`, the integral tail is eventually nonempty. -/
theorem eventually_upperTailLength_pos {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < upperTailLength c n :=
  (upperTailLength_tendsto_atTop hc).eventually (eventually_gt_atTop 0)

/-- Ceiling changes `c n/log n` only by a negligible relative error. -/
theorem upperTailLength_normalized_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailLength c n : ℝ) / secondOrderScale n)
      atTop (nhds c) := by
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
      secondOrderScale_tendsto_atTop

/-- The chosen upper tail is `o(n)`. -/
theorem upperTailLength_ratio_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    (upperTailLength_normalized_tendsto hc).mul
      secondOrderScale_ratio_tendsto_zero
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hscaleNe : secondOrderScale n ≠ 0 := hscale.ne'
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- Hence the chosen tail length is eventually at most `n`. -/
theorem eventually_upperTailLength_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, upperTailLength c n ≤ n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcast : (upperTailLength c n : ℝ) ≤ (n : ℝ) := by
    have hratioLe :
        (upperTailLength c n : ℝ) / (n : ℝ) ≤ 1 := hratio.le
    have := (div_le_iff₀ hnReal).mp hratioLe
    simpa only [one_mul] using this
  exact_mod_cast hcast



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/





















/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod



/-- The defining quotient for `roughHeadBalancedAlpha` gives the exact
real-length balance as soon as the high block has positive length. -/
theorem roughHeadBalancedAlpha_length_normalization
    {W n h K : ℕ} {beta L : ℝ} (hKhPos : 0 < K * h) :
    roughHeadDensity W *
        (roughHeadBalancedAlpha W n h K beta L *
            (((K * h : ℕ) : ℝ)) +
          (beta / L) * (((n - K * h : ℕ) : ℝ))) =
      ((h : ℕ) : ℝ) := by
  have hdelta : roughHeadDensity W ≠ 0 :=
    (roughHeadDensity_pos W).ne'
  have hKhReal : (((K * h : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hKhPos.ne'
  rw [roughHeadBalancedAlpha, div_mul_cancel₀ _ hKhReal,
    sub_add_cancel]
  calc
    roughHeadDensity W * (((h : ℕ) : ℝ) / roughHeadDensity W) =
        ((((h : ℕ) : ℝ) * roughHeadDensity W) /
          roughHeadDensity W) := by ring
    _ = ((h : ℕ) : ℝ) := mul_div_cancel_right₀ _ hdelta































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPaperComponents -/
section


/-!
# Actual bottom-bank components from the concrete marker matching

The capacity argument deliberately matches the rectangular upper-bound family
consisting of every signed slot and all four bottom rows.  The path belonging
to a small source prime does not use every one of those rows: source `3` uses
only `3→2→1`, and source `2` uses only `2→1`.  This file therefore separates
the full matched family from the literal relevant subfamily before forming any
set of used occurrences.

For every matched request we retain its actual prime marker, the two state
factors in the corresponding row, and its donor occurrence.  A finite set of
occurrence values is used, so in the last two rows the donor and the upper
state are literally one occurrence, rather than two tagged copies.  The only
global input is the already constructed injective marker matching.  All other
claims below are explicit interval, factorization, and large-prime arithmetic.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal relevant subfamily -/





















































/-! ## The deterministic truncated bottom path -/

























/-! ## A realization obtained from the actual matching -/





namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)





























/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/









namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)























































end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/



























end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/







/-! ## Eventual local geometry and the terminal realized family -/

private theorem bankBottom_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

theorem eventually_bankBottom_six_le_yNat :
    ∀ᶠ n : ℕ in atTop, 6 ≤ yNat n :=
  bankBottom_yNat_tendsto_atTop.eventually (eventually_ge_atTop 6)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector -/
section


/-!
# One-shot Section 8 orchestration for the two zero-head cells

This file joins the three already audited layers of the literal Section 8
construction:

* the analytic ledger gives the `q0` and integer-height asymptotics;
* the two-zero-cell producer realizes the height change by `-d / 2` in
  each physical copy of the zero head cell; and
* the structured prebridge ledger transports the resulting integral row
  change and the exact head-prime moments.

The source selector is not postulated through a new interface.  It is the
canonical protected-plus-ambient selector, and its finite selector state is
read directly from the existing
`BankPaperCanonicalRoundedSelectorTangentInput`.  Consequently the only
new feasibility work is at the two coordinates that actually change.

The terminal eventual theorem uses the same `hcanonical` and
`cellMassMargin` arguments as the canonical Proposition 8.7 statement.  It
only assumes that the ledger and rough guard agree on the positive, smooth,
at-most-`2n` structured universe.  Together with the canonical sample guards,
this yields pointwise exclusion from the full rough guard without any global
Finset equality.  To invoke the existing actual P87 endpoint consumer after
the structured placement, one must additionally identify
the rebalanced seed with a bridge baseline (`Hmeasure` and `hseed`) and
supply the existing analytic `Hfit`; those are retained under their
existing names rather than hidden in a new assumption package.
-/

open Filter Topology Asymptotics Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A reusable two-cell scalar capacity lemma -/



/-! ## Height-only capacity from the Section 8 ledger -/









/-! ## Reusing the rounded source selector -/







/-! ## Exact quota transport -/











/-! ## Canonical P87-local one-shot orchestration -/

/-- A fixed multiple of the upper-tail length is eventually at most the
ambient sample size. -/
theorem eventually_mul_upperTailLength_le_self
    (K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      K * upperTailLength c n <= n := by
  have hT : Tendsto
      (fun n : Nat => (K : Real) *
        ((upperTailLength c n : Real) / (n : Real)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
  have hsmall := hT.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnPos
  have hn' :
      (K : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := hn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hnPos
  have hnDiv :
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) < 1 := by
    calc
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) =
          (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) := by ring
      _ < 1 := hn'
  have hcross :
      (K : Real) * (upperTailLength c n : Real) < (n : Real) := by
    simpa only [one_mul] using (div_lt_iff₀ hnReal).mp hnDiv
  have hcast :
      ((K * upperTailLength c n : Nat) : Real) < (n : Real) := by
    push_cast
    exact hcross
  exact_mod_cast hcast.le







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale -/
section


/-!
# Canonical sharp Saias row-scale geometry

This file specializes the closed sharp endpoint and fixed-head estimates to
the paper's literal balanced raw point.  The high-block multiplicity is
written as `K0 + 1`, so its positivity is built into the data rather than
assumed separately.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Uniform control of the literal balanced coefficient -/



/-- A lower bound for the integral tail gives a constant bound for the
balanced high-block coefficient. -/
theorem roughHeadBalancedAlpha_abs_le_of_tail_lower
    {W n h K : ℕ} {beta L c : ℝ}
    (hc : 0 < c) (hn : 0 < n) (hK : 0 < K) (hL : 0 < L)
    (htail : c * (n : ℝ) / L ≤ (h : ℝ)) :
    |roughHeadBalancedAlpha W n h K beta L| ≤
      1 / ((K : ℝ) * roughHeadDensity W) +
        |beta| / ((K : ℝ) * c) := by
  have hdelta : 0 < roughHeadDensity W := roughHeadDensity_pos W
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have htailPos : 0 < c * (n : ℝ) / L := by positivity
  have hhReal : (0 : ℝ) < (h : ℝ) := htailPos.trans_le htail
  have hden :
      0 < (K : ℝ) * (h : ℝ) := mul_pos hKReal hhReal
  have hsubCast :
      (((n - K * h : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n (K * h)
  have hsubCastNonneg :
      (0 : ℝ) ≤ (((n - K * h : ℕ) : ℝ)) := by
    positivity
  have hnum :
      |(h : ℝ) / roughHeadDensity W -
          (beta / L) * (((n - K * h : ℕ) : ℝ))| ≤
        (h : ℝ) / roughHeadDensity W +
          |beta| / L * (n : ℝ) := by
    calc
      |(h : ℝ) / roughHeadDensity W -
          (beta / L) * (((n - K * h : ℕ) : ℝ))| ≤
        |(h : ℝ) / roughHeadDensity W| +
          |(beta / L) * (((n - K * h : ℕ) : ℝ))| :=
        abs_sub _ _
      _ = (h : ℝ) / roughHeadDensity W +
          (|beta| / L) * (((n - K * h : ℕ) : ℝ)) := by
        rw [abs_div, abs_of_pos hdelta, abs_of_nonneg hhReal.le,
          abs_mul, abs_div, abs_of_pos hL,
          abs_of_nonneg hsubCastNonneg]
      _ ≤ (h : ℝ) / roughHeadDensity W +
          |beta| / L * (n : ℝ) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hsubCast
            (div_nonneg (abs_nonneg beta) hL.le))
  have hcross : c * (n : ℝ) ≤ (h : ℝ) * L := by
    have := (div_le_iff₀ hL).mp htail
    simpa only [mul_comm] using this
  have hnDiv : (n : ℝ) ≤ ((h : ℝ) * L) / c :=
    (le_div_iff₀ hc).2 (by
      calc
        (n : ℝ) * c = c * (n : ℝ) := by ring
        _ ≤ (h : ℝ) * L := hcross)
  have hratio :
      (n : ℝ) / ((h : ℝ) * L) ≤ 1 / c := by
    calc
      (n : ℝ) / ((h : ℝ) * L) ≤
          (((h : ℝ) * L) / c) / ((h : ℝ) * L) :=
        div_le_div_of_nonneg_right hnDiv
          (mul_nonneg hhReal.le hL.le)
      _ = 1 / c := by field_simp
  unfold roughHeadBalancedAlpha
  norm_num only [Nat.cast_mul]
  rw [abs_div, abs_of_pos hden]
  calc
    |(h : ℝ) / roughHeadDensity W -
        (beta / L) * (((n - K * h : ℕ) : ℝ))| /
          ((K : ℝ) * (h : ℝ)) ≤
      ((h : ℝ) / roughHeadDensity W +
        |beta| / L * (n : ℝ)) /
          ((K : ℝ) * (h : ℝ)) :=
        (div_le_div_iff_of_pos_right hden).2 hnum
    _ = 1 / ((K : ℝ) * roughHeadDensity W) +
        (|beta| / (K : ℝ)) *
          ((n : ℝ) / ((h : ℝ) * L)) := by
      field_simp [hdelta.ne', hKReal.ne', hhReal.ne', hL.ne']
    _ ≤ 1 / ((K : ℝ) * roughHeadDensity W) +
        (|beta| / (K : ℝ)) * (1 / c) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hratio
          (div_nonneg (abs_nonneg beta) hKReal.le))
    _ = 1 / ((K : ℝ) * roughHeadDensity W) +
        |beta| / ((K : ℝ) * c) := by
      field_simp [hKReal.ne', hc.ne']

/-- With the paper tail and the positive multiplicity `K0+1`, the
balanced coefficient is uniformly bounded by a constant chosen before
`n`. -/
theorem roughHeadBalancedAlpha_succ_abs_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n : ℕ} (hn : 2 ≤ n) :
    |roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
        beta (L n)| ≤
      1 / (((K0 + 1 : ℕ) : ℝ) * roughHeadDensity W) +
        |beta| / (((K0 + 1 : ℕ) : ℝ) * c) := by
  have hL : 0 < L n := L_pos (by omega)
  have htail :
      c * (n : ℝ) / L n ≤ (upperTailLength c n : ℝ) := by
    rw [upperTailLength]
    calc
      c * (n : ℝ) / L n = c * secondOrderScale n := by
        unfold secondOrderScale L
        ring
      _ ≤ (Nat.ceil (c * secondOrderScale n) : ℝ) :=
        Nat.le_ceil (c * secondOrderScale n)
  exact roughHeadBalancedAlpha_abs_le_of_tail_lower
    hc (by omega) (by omega) hL htail

/-! ## Fixed constants for the three row ledgers -/



theorem roughBalancedAlphaConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughBalancedAlphaConstant W K0 c beta := by
  unfold roughBalancedAlphaConstant
  have hK : (0 : ℝ) <
      (((K0 + 1 : ℕ) : ℝ)) := by positivity
  have hdelta : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  positivity











/-! ## Quotient and logarithmic geometry -/





























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenInitialMassConnector -/
section


/-!
# Initial selector mass from the frozen-top smooth-row bridge

This connector is the asymptotic integration boundary for the separate
`qTilde`-stage source constructed in
`BankPaperCanonicalSectionEightTopFrozenSourceConnector`.

The family-facing premise below is an exact construction equation:
the initial selector has the same guarded label-one row sum as the balanced
literal raw selector.  Together with the existing exact nonsmooth-row state,
the charged row ledger reduces the whole selector-mass error to:

* the balanced raw label-one discrepancy;
* the two charged label-one multiplicities; and
* the balanced raw mass deleted by the numerical guard.

The first term is handled by the sharp Saias row theorem.  Fixed exceptional
factors and bank bases have zero label-one multiplicity in the paper range.
The remaining deleted row is contained in the promoted smooth residual
anchors, hence has cardinality at most `yNat`; the existing uniform balanced
raw-weight bound then absorbs it into `secondOrderScale / L`.

No final-selector quota, height displacement, or Section 9 source state is
used here.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The balanced raw selector used by the initial-mass interface -/



/-! ## The two charged smooth-row multiplicities -/





/-! ## Full label-one guard deletion -/









/-! ## Paper-scale bounds for the smooth row -/

private theorem topFrozenInitialMass_L_tendsto_atTop :
    Tendsto L atTop atTop := by
  simpa only [L] using
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Eventually the logarithm of every possible label-one quotient endpoint
(which is at most `3n`) lies in the five-log-`yNat` analytic chamber. -/
theorem eventually_log_three_mul_natCast_le_five_log_yNat :
    ∀ᶠ n : Nat in atTop,
      Real.log (3 * (n : Real)) <=
        5 * Real.log (yNat n : Real) := by
  have hLlarge : ∀ᶠ n : Nat in atTop,
      9 * Real.log 3 + 45 * Real.log 2 <= L n :=
    topFrozenInitialMass_L_tendsto_atTop.eventually
      (eventually_ge_atTop
        (9 * Real.log 3 + 45 * Real.log 2))
  filter_upwards [eventually_gt_atTop 0,
      eventually_bankBottom_six_le_yNat, hLlarge]
      with n hn hySix hLlargeN
  have hyPos : 0 < y n := y_pos hn
  have hyFloor : (yNat n : Real) <= y n :=
    Nat.floor_le hyPos.le
  have hyRealTwo : (2 : Real) <= y n := by
    exact
      (by exact_mod_cast (show 2 <= yNat n by omega) :
        (2 : Real) <= (yNat n : Real)).trans hyFloor
  have hyNatLower : y n / 2 <= (yNat n : Real) := by
    have hfloor : y n < (yNat n : Real) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  have hlogLower :
      Real.log (y n / 2) <= Real.log (yNat n : Real) :=
    Real.log_le_log (div_pos hyPos (by norm_num)) hyNatLower
  have hlogDiv :
      Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hyPos.ne' (by norm_num : (2 : Real) ≠ 0)]
  calc
    Real.log (3 * (n : Real)) = Real.log 3 + L n := by
      rw [Real.log_mul (by norm_num : (3 : Real) ≠ 0)
        (by exact_mod_cast hn.ne')]
      rfl
    _ <= 5 * Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      nlinarith
    _ <= 5 * Real.log (yNat n : Real) := by
      gcongr







/-! ## Exact construction boundary and the charged mass ledger -/





/-! ## Asymptotic initial-selector mass theorem -/



/-! ## The concrete WithTop/scaled-seed constructor -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalBalancedRawSignedValuationResidualBoundConnector -/
section


/-!
# The balanced raw signed valuation residual

The raw signed residual is the one generic term left as a premise in the
four-term paper-rate closure.  This file proves it directly from the
elementary fixed-modulus interval count.

For a fixed prime `p`, every valuation is expanded into the indicators of
`p ^ k` divisibility.  At one exponent, the upper interval has endpoint
error less than one, while each of the two head-free lower intervals has
error at most `roughHeadModulus W + 1`.  The three real-length main terms
cancel exactly by `roughHeadBalancedAlpha_length_normalization`.

The resulting finite bound is logarithmic in the physical endpoint.  The
last section absorbs that logarithm uniformly for `p <= yNat n` into the
paper scale `secondOrderScale n / (p * L n)`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Valuations as finite prime-power column sums -/

private theorem raw_factorization_le_log_of_le
    {a M p : Nat} (ha : 0 < a) (haM : a <= M) (hp : p.Prime) :
    a.factorization p <= Nat.log p M := by
  have hpowDvd : p ^ (a.factorization p) ∣ a :=
    (hp.pow_dvd_iff_le_factorization ha.ne').mpr le_rfl
  have hpowLe : p ^ (a.factorization p) <= a :=
    Nat.le_of_dvd ha hpowDvd
  exact (Nat.le_log_of_pow_le hp.one_lt hpowLe).trans
    (Nat.log_mono_right haM)

/-- Public finite expansion of a valuation into its prime-power divisibility
indicators.  The endpoint `M` only has to dominate the positive integer
being expanded. -/
theorem factorization_cast_eq_sum_primeExponentIndicators
    {a M p : Nat} (ha : 0 < a) (haM : a <= M) (hp : p.Prime) :
    (a.factorization p : Real) =
      ∑ k ∈ primeExponentRange p M,
        if p ^ k ∣ a then (1 : Real) else 0 := by
  classical
  have hfac : a.factorization p <= Nat.log p M :=
    raw_factorization_le_log_of_le ha haM hp
  have hfilter :
      (primeExponentRange p M).filter (fun k => p ^ k ∣ a) =
        Finset.Icc 1 (a.factorization p) := by
    ext k
    simp only [primeExponentRange, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk, _⟩, hdvd⟩
      exact ⟨hk, (hp.pow_dvd_iff_le_factorization ha.ne').mp hdvd⟩
    · rintro ⟨hk, hkfac⟩
      exact ⟨⟨hk, hkfac.trans hfac⟩,
        (hp.pow_dvd_iff_le_factorization ha.ne').mpr hkfac⟩
  calc
    (a.factorization p : Real) =
        ((Finset.Icc 1 (a.factorization p)).card : Real) := by simp
    _ = (((primeExponentRange p M).filter
        (fun k => p ^ k ∣ a)).card : Real) := by rw [hfilter]
    _ = ∑ k ∈ primeExponentRange p M,
        if p ^ k ∣ a then (1 : Real) else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Summing the preceding pointwise expansion turns an unweighted valuation
sum into the cardinalities of its prime-power divisor fibers. -/
theorem sum_factorization_cast_eq_sum_primePowerDivisorCounts
    {A : Finset Nat} {M p : Nat}
    (hpos : ∀ a ∈ A, 0 < a) (hle : ∀ a ∈ A, a <= M)
    (hp : p.Prime) :
    (∑ a ∈ A, (a.factorization p : Real)) =
      ∑ k ∈ primeExponentRange p M,
        (((A.filter (fun a => p ^ k ∣ a)).card : Nat) : Real) := by
  classical
  calc
    (∑ a ∈ A, (a.factorization p : Real)) =
        ∑ a ∈ A, ∑ k ∈ primeExponentRange p M,
          if p ^ k ∣ a then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact factorization_cast_eq_sum_primeExponentIndicators
        (hpos a ha) (hle a ha) hp
    _ = ∑ k ∈ primeExponentRange p M, ∑ a ∈ A,
          if p ^ k ∣ a then (1 : Real) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ primeExponentRange p M,
        (((A.filter (fun a => p ^ k ∣ a)).card : Nat) : Real) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]

/-- Weighted companion of
`sum_factorization_cast_eq_sum_primePowerDivisorCounts`. -/
theorem sum_weight_mul_factorization_cast_eq_sum_primePowerIndicators
    {A : Finset Nat} {M p : Nat} (weight : Nat -> Real)
    (hpos : ∀ a ∈ A, 0 < a) (hle : ∀ a ∈ A, a <= M)
    (hp : p.Prime) :
    (∑ a ∈ A, weight a * (a.factorization p : Real)) =
      ∑ k ∈ primeExponentRange p M, ∑ a ∈ A,
        weight a * (if p ^ k ∣ a then (1 : Real) else 0) := by
  classical
  calc
    (∑ a ∈ A, weight a * (a.factorization p : Real)) =
        ∑ a ∈ A, weight a *
          (∑ k ∈ primeExponentRange p M,
            if p ^ k ∣ a then (1 : Real) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [factorization_cast_eq_sum_primeExponentIndicators
        (hpos a ha) (hle a ha) hp]
    _ = ∑ a ∈ A, ∑ k ∈ primeExponentRange p M,
          weight a * (if p ^ k ∣ a then (1 : Real) else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = ∑ k ∈ primeExponentRange p M, ∑ a ∈ A,
        weight a * (if p ^ k ∣ a then (1 : Real) else 0) := by
      rw [Finset.sum_comm]

/-! ## The literal one-column residual -/





/-- On a fixed prime-power column, summing the literal raw weight is exactly
the weighted sum of the two head-free interval counts. -/
theorem sum_roughHeadCompatibleRawWeight_mul_primePowerIndicator
    (W n h K : Nat) (alpha beta ell : Real) (p k : Nat) :
    (∑ a ∈ roughRawCandidateSet n h K,
      roughHeadCompatibleRawWeight W n h K alpha beta ell a *
        (if p ^ k ∣ a then (1 : Real) else 0)) =
      alpha *
        ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
          (2 * n - K * h) (2 * n)).card : Real) +
      (beta / ell) *
        ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
          n (2 * n - K * h)).card : Real) := by
  classical
  have hdisjoint :=
    roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K
  have hhigh :
      (∑ a ∈ roughHighLowerBlock n h K,
        roughHeadCompatibleRawWeight W n h K alpha beta ell a *
          (if p ^ k ∣ a then (1 : Real) else 0)) =
        alpha *
          ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
            (2 * n - K * h) (2 * n)).card : Real) := by
    calc
      (∑ a ∈ roughHighLowerBlock n h K,
        roughHeadCompatibleRawWeight W n h K alpha beta ell a *
          (if p ^ k ∣ a then (1 : Real) else 0)) =
          ∑ a ∈ roughHighLowerBlock n h K,
            if p ^ k ∣ a ∧ Nat.Coprime a (roughHeadModulus W)
              then alpha else 0 := by
        apply Finset.sum_congr rfl
        intro a haHigh
        have haBroad : a ∉ roughBroadLowerBlock n h K := by
          intro haBroad
          exact Finset.disjoint_left.mp hdisjoint haHigh haBroad
        by_cases hdiv : p ^ k ∣ a <;>
          by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hdiv, hcop]
      _ = alpha *
          ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
            (2 * n - K * h) (2 * n)).card : Real) := by
        rw [← Finset.sum_filter]
        simp [coprimeMultipleIoc, roughHighLowerBlock]
        ring
  have hbroad :
      (∑ a ∈ roughBroadLowerBlock n h K,
        roughHeadCompatibleRawWeight W n h K alpha beta ell a *
          (if p ^ k ∣ a then (1 : Real) else 0)) =
        (beta / ell) *
          ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
            n (2 * n - K * h)).card : Real) := by
    calc
      (∑ a ∈ roughBroadLowerBlock n h K,
        roughHeadCompatibleRawWeight W n h K alpha beta ell a *
          (if p ^ k ∣ a then (1 : Real) else 0)) =
          ∑ a ∈ roughBroadLowerBlock n h K,
            if p ^ k ∣ a ∧ Nat.Coprime a (roughHeadModulus W)
              then beta / ell else 0 := by
        apply Finset.sum_congr rfl
        intro a haBroad
        have haHigh : a ∉ roughHighLowerBlock n h K := by
          intro haHigh
          exact Finset.disjoint_left.mp hdisjoint haHigh haBroad
        by_cases hdiv : p ^ k ∣ a <;>
          by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hdiv, hcop]
      _ = (beta / ell) *
          ((coprimeMultipleIoc (roughHeadModulus W) (p ^ k)
            n (2 * n - K * h)).card : Real) := by
        rw [← Finset.sum_filter]
        simp [coprimeMultipleIoc, roughBroadLowerBlock]
        ring
  rw [roughRawCandidateSet, Finset.sum_union hdisjoint, hhigh, hbroad]

/-- Exact prime-power-column expansion of the raw signed valuation
residual. -/
theorem roughCanonicalRawSignedValuationResidual_eq_sum_primePowerColumns
    (W n h K : Nat) (alpha beta ell : Real) (p : Nat)
    (hp : p.Prime) :
    roughCanonicalRawSignedValuationResidual n h K
        (roughHeadCompatibleRawWeight W n h K alpha beta ell) p =
      ∑ k ∈ primeExponentRange p (2 * n + h),
        roughCanonicalRawPrimePowerColumnResidual
          W n h K alpha beta ell p k := by
  classical
  have hupperPos :
      ∀ a ∈ roughUpperBlock n h, 0 < a := by
    intro a ha
    simp only [roughUpperBlock, Finset.mem_Ioc] at ha
    omega
  have hupperLe :
      ∀ a ∈ roughUpperBlock n h, a <= 2 * n + h := by
    intro a ha
    exact (Finset.mem_Ioc.mp ha).2
  have hrawPos :
      ∀ a ∈ roughRawCandidateSet n h K, 0 < a := by
    intro a ha
    simp only [roughRawCandidateSet, roughHighLowerBlock,
      roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc] at ha
    omega
  have hrawLe :
      ∀ a ∈ roughRawCandidateSet n h K, a <= 2 * n + h := by
    intro a ha
    simp only [roughRawCandidateSet, roughHighLowerBlock,
      roughBroadLowerBlock, Finset.mem_union, Finset.mem_Ioc] at ha
    omega
  have hupper :=
    sum_factorization_cast_eq_sum_primePowerDivisorCounts
      hupperPos hupperLe hp
  have hlower :=
    sum_weight_mul_factorization_cast_eq_sum_primePowerIndicators
      (roughHeadCompatibleRawWeight W n h K alpha beta ell)
      hrawPos hrawLe hp
  unfold roughCanonicalRawSignedValuationResidual
  rw [hupper, hlower, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_roughHeadCompatibleRawWeight_mul_primePowerIndicator]
  unfold roughCanonicalRawPrimePowerColumnResidual
  ring



/-- Finite logarithmic bound for the complete raw signed valuation residual.
No asymptotic estimate occurs in this theorem. -/
theorem abs_roughCanonicalRawSignedValuationResidual_le_log_mul_columnBound
    {W n h K p : Nat} {alpha beta ell : Real}
    (hKh : K * h <= n)
    (hnormalization :
      roughHeadDensity W *
          (alpha * ((K * h : Nat) : Real) +
            (beta / ell) * ((n - K * h : Nat) : Real)) =
        (h : Real))
    (hp : p.Prime) (hWp : W < p) :
    abs (roughCanonicalRawSignedValuationResidual n h K
      (roughHeadCompatibleRawWeight W n h K alpha beta ell) p) <=
      (Nat.log p (2 * n + h) : Real) *
        (1 +
          abs alpha * ((roughHeadModulus W : Real) + 1) +
          abs (beta / ell) * ((roughHeadModulus W : Real) + 1)) := by
  rw [roughCanonicalRawSignedValuationResidual_eq_sum_primePowerColumns
    W n h K alpha beta ell p hp]
  calc
    abs (∑ k ∈ primeExponentRange p (2 * n + h),
        roughCanonicalRawPrimePowerColumnResidual
          W n h K alpha beta ell p k) <=
      ∑ k ∈ primeExponentRange p (2 * n + h),
        abs (roughCanonicalRawPrimePowerColumnResidual
          W n h K alpha beta ell p k) := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ <=
      ∑ _k ∈ primeExponentRange p (2 * n + h),
        (1 +
          abs alpha * ((roughHeadModulus W : Real) + 1) +
          abs (beta / ell) * ((roughHeadModulus W : Real) + 1)) := by
        apply Finset.sum_le_sum
        intro k _
        exact abs_roughCanonicalRawPrimePowerColumnResidual_le
          hKh hnormalization hp hWp
    _ =
      (Nat.log p (2 * n + h) : Real) *
        (1 +
          abs alpha * ((roughHeadModulus W : Real) + 1) +
          abs (beta / ell) * ((roughHeadModulus W : Real) + 1)) := by
        simp [primeExponentRange]
        ring

/-! ## Fixed constants for the balanced point -/



theorem roughCanonicalBalancedRawPrimePowerColumnConstant_nonneg
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <= roughCanonicalBalancedRawPrimePowerColumnConstant
      W K0 c beta := by
  unfold roughCanonicalBalancedRawPrimePowerColumnConstant
  have hAlpha :
      0 <= roughBalancedAlphaConstant W K0 c beta :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  positivity



theorem roughCanonicalBalancedRawSignedValuationConstant_nonneg
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <= roughCanonicalBalancedRawSignedValuationConstant
      W K0 c beta := by
  unfold roughCanonicalBalancedRawSignedValuationConstant
  exact mul_nonneg
    (div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
    (roughCanonicalBalancedRawPrimePowerColumnConstant_nonneg
      W K0 hc)

/-- The squared smooth cutoff is eventually bounded by the exact
`secondOrderScale / L` scale.  This is the stronger intermediate estimate
behind the previously exported linear cutoff bound. -/
theorem eventually_yNat_sq_le_secondOrderScale_div_L :
    ∀ᶠ n : Nat in atTop,
      (yNat n : Real) ^ 2 <= secondOrderScale n / L n := by
  have hratio := tendsto_endpointRatio_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hratio, eventually_ge_atTop 2]
      with n hratioN hn
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hL : 0 < L n := L_pos hn
  have hyNonneg : 0 <= y n := (y_pos hnPos).le
  have hyFloor : (yNat n : Real) <= y n :=
    Nat.floor_le hyNonneg
  have hySq : (yNat n : Real) ^ 2 <= y n ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hyNonneg).2 hyFloor
  have hratioNat :
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <= 1 := by
    calc
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <=
          y n ^ 2 * L n ^ 2 / (n : Real) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hySq (sq_nonneg _)) hnReal.le
      _ = endpointRatio n := by rfl
      _ <= 1 := hratioN.le
  have hySqScale :
      (yNat n : Real) ^ 2 <= (n : Real) / L n ^ 2 := by
    apply (le_div_iff₀ (pow_pos hL 2)).2
    have hcross := (div_le_iff₀ hnReal).1 hratioNat
    simpa only [one_mul] using hcross
  have htarget :
      (n : Real) / L n ^ 2 = secondOrderScale n / L n := by
    unfold secondOrderScale L
    ring
  exact hySqScale.trans_eq htarget

/-- The balanced one-column error is eventually bounded by the fixed
constant chosen before `n` and `p`. -/
theorem eventually_balancedRaw_primePowerColumnBound_le_constant
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      1 +
          abs (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n)) *
            ((roughHeadModulus W : Real) + 1) +
          abs (beta / L n) * ((roughHeadModulus W : Real) + 1) <=
        roughCanonicalBalancedRawPrimePowerColumnConstant
          W K0 c beta := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
      hLTop.eventually (eventually_ge_atTop (1 : Real))]
      with n hn hL
  have halpha :
      abs (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n)) <=
        roughBalancedAlphaConstant W K0 c beta := by
    simpa only [roughBalancedAlphaConstant] using
      roughHeadBalancedAlpha_succ_abs_le W K0 (beta := beta) hc hn
  have hLPos : 0 < L n := zero_lt_one.trans_le hL
  have hbetaDiv : abs (beta / L n) <= abs beta := by
    rw [abs_div, abs_of_pos hLPos]
    apply (div_le_iff₀ hLPos).2
    nlinarith [abs_nonneg beta]
  have hperiod :
      0 <= (roughHeadModulus W : Real) + 1 := by positivity
  unfold roughCanonicalBalancedRawPrimePowerColumnConstant
  calc
    1 +
        abs (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n)) *
          ((roughHeadModulus W : Real) + 1) +
        abs (beta / L n) * ((roughHeadModulus W : Real) + 1) <=
      1 +
        roughBalancedAlphaConstant W K0 c beta *
          ((roughHeadModulus W : Real) + 1) +
        abs beta * ((roughHeadModulus W : Real) + 1) := by
      exact add_le_add
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right halpha hperiod))
        (mul_le_mul_of_nonneg_right hbetaDiv hperiod)
    _ =
      1 +
        (roughBalancedAlphaConstant W K0 c beta + abs beta) *
          ((roughHeadModulus W : Real) + 1) := by ring

/-! ## Eventual paper-rate absorption -/

/-- Explicit eventual paper-rate estimate for the balanced raw signed
valuation residual, uniform over every medium prime above the fixed head. -/
theorem eventually_roughCanonicalBalancedRawSignedValuationResidualBound
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop, ∀ p : Nat,
      p.Prime -> W < p -> p <= yNat n ->
      RoughCanonicalBalancedRawSignedValuationResidualBound
        W n K0 c beta p
        (roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
          secondOrderScale n / ((p : Real) * L n)) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
      eventually_ge_atTop 2,
      eventually_mul_upperTailLength_le_self (K0 + 1) hc,
      eventually_upperTailLength_pos hc,
      eventually_upperTailLength_le hc,
      hLTop.eventually (eventually_ge_atTop (1 : Real)),
      eventually_log_three_mul_natCast_le_five_log_yNat,
      eventually_yNat_sq_le_secondOrderScale_div_L,
      eventually_bankBottom_six_le_yNat,
      eventually_balancedRaw_primePowerColumnBound_le_constant
        W K0 hc]
      with n hn hKh htailPos htailLe hLOne hlogThree
        hySq hySix hcolumn
  intro p hp hWp hpY
  have hKhPos :
      0 < (K0 + 1) * upperTailLength c n :=
    Nat.mul_pos (by omega) htailPos
  have hfinite :=
    abs_roughCanonicalRawSignedValuationResidual_le_log_mul_columnBound
      (W := W) (n := n) (h := upperTailLength c n)
      (K := K0 + 1) (p := p)
      (alpha := roughHeadBalancedAlpha W n (upperTailLength c n)
        (K0 + 1) beta (L n))
      (beta := beta) (ell := L n)
      hKh
      (roughHeadBalancedAlpha_length_normalization
        (W := W) (n := n) (h := upperTailLength c n)
        (K := K0 + 1) (beta := beta) (L := L n) hKhPos)
      hp hWp
  have hcolumnNonneg :
      0 <= roughCanonicalBalancedRawPrimePowerColumnConstant
        W K0 c beta :=
    roughCanonicalBalancedRawPrimePowerColumnConstant_nonneg
      W K0 hc
  have hrawLog :
      abs (roughCanonicalRawSignedValuationResidual n
        (upperTailLength c n) (K0 + 1)
        (roughHeadCompatibleRawWeight W n (upperTailLength c n)
          (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)) p) <=
        (Nat.log p (2 * n + upperTailLength c n) : Real) *
          roughCanonicalBalancedRawPrimePowerColumnConstant
            W K0 c beta := by
    exact hfinite.trans
      (mul_le_mul_of_nonneg_left hcolumn (Nat.cast_nonneg _))
  have hendpoint :
      2 * n + upperTailLength c n <= 3 * n := by omega
  have hendpointPos :
      0 < 2 * n + upperTailLength c n := by omega
  have hendpointReal :
      (2 * n + upperTailLength c n : Real) <=
        3 * (n : Real) := by
    exact_mod_cast hendpoint
  have hlogEndpoint :
      Real.log (2 * n + upperTailLength c n : Real) <=
        Real.log (3 * (n : Real)) :=
    Real.log_le_log (by exact_mod_cast hendpointPos) hendpointReal
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogCount :
      (Nat.log p (2 * n + upperTailLength c n) : Real) <=
        (5 / Real.log 2) * Real.log (yNat n : Real) := by
    calc
      (Nat.log p (2 * n + upperTailLength c n) : Real) <=
          (Nat.log 2 (2 * n + upperTailLength c n) : Real) := by
        exact_mod_cast
          (Nat.log_mono Nat.one_lt_two hp.two_le
            (le_refl (2 * n + upperTailLength c n)))
      _ <= Real.logb 2 (2 * n + upperTailLength c n : Nat) :=
        Real.natLog_le_logb (2 * n + upperTailLength c n) 2
      _ = Real.log (2 * n + upperTailLength c n : Real) /
          Real.log 2 := by
        simp only [Real.logb, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat]
      _ <= Real.log (3 * (n : Real)) / Real.log 2 :=
        (div_le_div_iff_of_pos_right hlogTwo).2 hlogEndpoint
      _ <= (5 * Real.log (yNat n : Real)) / Real.log 2 := by
        exact (div_le_div_iff_of_pos_right hlogTwo).2 hlogThree
      _ = (5 / Real.log 2) * Real.log (yNat n : Real) := by ring
  have hconstantNonneg :
      0 <= roughCanonicalBalancedRawSignedValuationConstant
        W K0 c beta :=
    roughCanonicalBalancedRawSignedValuationConstant_nonneg
      W K0 hc
  have hyPosNat : 0 < yNat n := by omega
  have hyPos : (0 : Real) < (yNat n : Real) := by
    exact_mod_cast hyPosNat
  have hlogYLeY :
      Real.log (yNat n : Real) <= (yNat n : Real) := by
    have hlogSub := Real.log_le_sub_one_of_pos hyPos
    linarith
  have hpReal : (0 : Real) < (p : Real) := by
    exact_mod_cast hp.pos
  have hpYReal : (p : Real) <= (yNat n : Real) := by
    exact_mod_cast hpY
  have hpMulY :
      (p : Real) * (yNat n : Real) <= (yNat n : Real) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_right hpYReal (Nat.cast_nonneg _)
  have hLPos : 0 < L n := zero_lt_one.trans_le hLOne
  have hyTarget :
      (yNat n : Real) <=
        secondOrderScale n / ((p : Real) * L n) := by
    apply (le_div_iff₀ (mul_pos hpReal hLPos)).2
    calc
      (yNat n : Real) * ((p : Real) * L n) =
          ((p : Real) * (yNat n : Real)) * L n := by ring
      _ <= (yNat n : Real) ^ 2 * L n :=
        mul_le_mul_of_nonneg_right hpMulY hLPos.le
      _ <= (secondOrderScale n / L n) * L n :=
        mul_le_mul_of_nonneg_right hySq hLPos.le
      _ = secondOrderScale n := div_mul_cancel₀ _ hLPos.ne'
  unfold RoughCanonicalBalancedRawSignedValuationResidualBound
  calc
    abs (roughCanonicalRawSignedValuationResidual n
        (upperTailLength c n) (K0 + 1)
        (roughHeadCompatibleRawWeight W n (upperTailLength c n)
          (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)) p) <=
      (Nat.log p (2 * n + upperTailLength c n) : Real) *
        roughCanonicalBalancedRawPrimePowerColumnConstant
          W K0 c beta := hrawLog
    _ <=
      ((5 / Real.log 2) * Real.log (yNat n : Real)) *
        roughCanonicalBalancedRawPrimePowerColumnConstant
          W K0 c beta :=
      mul_le_mul_of_nonneg_right hlogCount hcolumnNonneg
    _ =
      roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
        Real.log (yNat n : Real) := by
      unfold roughCanonicalBalancedRawSignedValuationConstant
      ring
    _ <=
      roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
        (yNat n : Real) :=
      mul_le_mul_of_nonneg_left hlogYLeY hconstantNonneg
    _ <=
      roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
        (secondOrderScale n / ((p : Real) * L n)) :=
      mul_le_mul_of_nonneg_left hyTarget hconstantNonneg
    _ =
      roughCanonicalBalancedRawSignedValuationConstant W K0 c beta *
          secondOrderScale n / ((p : Real) * L n) := by ring



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ (W K0 : Nat) {c beta : Real},
  LT.lt.{0} (0 : Real) c →
    ∀ᶠ (n : Nat) in Filter.atTop.{0},
      ∀ (p : Nat),
        Nat.Prime p →
          LT.lt.{0} W p →
            LE.le.{0} p (Erdos390.Full.ArithmeticModel.yNat n) →
              Erdos390.WholePaper.BankPaperRealization.RoughCanonicalBalancedRawSignedValuationResidualBound W n K0 c
                beta p
                (HDiv.hDiv.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0}
                    (Erdos390.WholePaper.BankPaperRealization.roughCanonicalBalancedRawSignedValuationConstant W K0 c
                      beta)
                    (Erdos390.WholePaper.secondOrderScale n))
                  (HMul.hMul.{0, 0, 0} (↑p) (Erdos390.Full.Scale.L n))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.eventually_roughCanonicalBalancedRawSignedValuationResidualBound
