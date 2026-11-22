-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.3459+00:00
-- url     : https://prove2.me/submissions/8c0774f7-42f0-4fa7-8457-cd3b2847194f

import Definitions.Def_erdos390_remaining_analytic_propositions_005
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate_compact
import Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact




section
theorem Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower : Erdos390.RemainingAnalyticGoal008_004 := @Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact
end
section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate : Erdos390.RemainingAnalyticGoal007_004.{u_1} := @Erdos390.WholePaper.BankPaperRealization.exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate : Erdos390.RemainingAnalyticGoal007_002 := @Erdos390.WholePaper.BankPaperRealization.exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate_compact
end
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



































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger -/
section


/-!
# The exact smooth-row quota and height ledger from Section 8

This file records the algebraic part of the paper's smooth-row initialization
without replacing any actual finite mass by an asymptotic main term.

The literal active base component is the constant weight `betaAct / L n` on
the head-free, `yNat n`-smooth part of the broad interval.  Its exact support
is the complete-rough row with label one.  The later definitions follow the
paper verbatim:

* `Q_sm(0)` is the nearest integer to `m_sm,fr + qTilde`, with a half-integer
  tie sent to the smaller integer;
* `q0 = Q_sm(0) - m_sm,fr`;
* `Q_sm(d) = Q_sm(0) - d` and `qAct(d) = q0 - d`;
* `A0 = logY - Lambda0 - q0 * L` and `A(d) = A0 + d * L`;
* `d` is the tie-lower nearest integer to
  `(mu * q0 - A0) / (L + mu)`.

All displayed identities and the two nearest-integer errors are unconditional.
The analytic comparison between the raw base mass and the actual post-guard
mass is deliberately left to the companion asymptotic module.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal rough smooth base component -/

















/-! ## Tie-lower nearest integers -/









/-- The universal half-unit rounding error. -/
theorem bankPaperNearestIntegerTieLower_abs_sub_le (x : Real) :
    |(bankPaperNearestIntegerTieLower x : Real) - x| ≤ 1 / 2 := by
  have hcell :=
    (bankPaperNearestIntegerTieLower_eq_iff x
      (bankPaperNearestIntegerTieLower x)).1 rfl
  apply abs_le.mpr
  constructor <;> linarith

/-! ## Exact smooth-row quota initialization -/







/-- Exact expression for the initialization error. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_sub_actual
    (mFrozen qTilde : Real) :
    bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde =
      (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
        (mFrozen + qTilde) := by
  unfold bankPaperCanonicalSmoothInitialActiveMass
  ring

/-- The paper's literal bound `|q0 - qTilde| <= 1/2`. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen qTilde : Real) :
    |bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde| ≤
      1 / 2 := by
  rw [bankPaperCanonicalSmoothInitialActiveMass_sub_actual]
  exact bankPaperNearestIntegerTieLower_abs_sub_le (mFrozen + qTilde)

















/-! ## Exact frozen-height ledger and centered adjustment -/











/-- The rounded height adjustment is within one half of `dStar`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
    (n : Nat) (mu q0 A0 : Real) :
    |(bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu q0 A0| ≤ 1 / 2 :=
  bankPaperNearestIntegerTieLower_abs_sub_le
    (bankPaperCanonicalSmoothHeightCenter n mu q0 A0)















/-! ## Literal Section 8 families -/



















/-- Family-level half-unit initialization error. -/
theorem bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
    (mFrozen qTilde : Nat -> Real) (n : Nat) :
    |bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - qTilde n| <=
      1 / 2 :=
  bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen n) (qTilde n)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/



/-- The fixed Dickman floor is strictly positive. -/
theorem roughCanonicalPoolDickmanFloor_pos :
    0 < roughCanonicalPoolDickmanFloor := by
  unfold roughCanonicalPoolDickmanFloor
  exact rho_pos_on_zero_five (by norm_num) le_rfl



/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/



/-- The retained raw broad-pool density is strictly positive. -/
theorem roughCanonicalRawBroadPoolDensity_pos (W : Nat) :
    0 < roughCanonicalRawBroadPoolDensity W := by
  unfold roughCanonicalRawBroadPoolDensity
  exact div_pos
    (mul_pos (roughHeadDensity_pos W)
      roughCanonicalPoolDickmanFloor_pos) (by norm_num)









/-! ## Uniform paper-scale choices -/























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalHeadActiveMassEventually -/
section


/-!
# Eventual lower bound for the paper's head-reserve active mass

The paper obtains its final active mass from the exact ledger

`q^{act}(d) = q₀ - d`,

where the rough smooth active mass satisfies `q₀ ≍ n / log n` and the
height-centering change satisfies `d = O(n / log² n)`.  Only the lower
half of that comparison is needed to prove the constructor hypothesis
`1 <= q^{act}(d)` for all sufficiently large `n`.

The repository's `HeadSimplexReserve` currently stores only
`0 < activeMass`.  It has no family constructor, no connection to the
rough smooth active mass, and no asymptotic lower-bound field.  This file
therefore isolates the exact missing paper input as a positive lower
multiple of `secondOrderScale n = n / log n`.  Everything after that input
is proved here:

* the active mass tends to infinity and eventually exceeds every constant;
* in particular it is eventually at least one;
* an `o(n / log n)` height change preserves a fixed positive lower multiple;
* the paper's stronger `O(n / log² n)` change is automatically little-o;
* the canonical scaled seed has eventual mass at least one and its
  self-selector satisfies the full actual-active-measure constructor.

A concrete reserve of mass `1 / 2` is also constructed.  It proves that
strict positivity alone cannot imply the desired inequality, so the
repository needs an additional growth input until the missing
rough-active-mass construction is connected to `HeadSimplexReserve`.
The predicate below is exactly the lower half of the growth statement
used in the paper.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

/-! ## The irreducible paper-scale input -/





/-! ## Positivity is genuinely insufficient -/









/-! ## All eventual consequences of the minimal input -/











/-! ## The exact `q₀-d` height-centering algebra -/

/-- The paper's error scale `n / log² n` is little-o of
`secondOrderScale n = n / log n`. -/
theorem secondOrderScale_div_L_isLittleO_secondOrderScale :
    (fun n : Nat => secondOrderScale n / L n) =o[atTop]
      secondOrderScale := by
  have hzero : ∀ᶠ n : Nat in atTop,
      secondOrderScale n = 0 -> secondOrderScale n / L n = 0 :=
    Eventually.of_forall fun n hn => by simp [hn]
  apply (isLittleO_iff_tendsto' hzero).mpr
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat => (L n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  apply hinv.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hL : 0 < L n := L_pos hn
  field_simp [hscale.ne', hL.ne']

/-- Subtracting a little-o height-centering change from a macroscopically
positive base mass preserves half of its lower constant. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =o[atTop] secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  rcases Hq0 with ⟨c, hc, hq0⟩
  refine ⟨c / 2, half_pos hc, ?_⟩
  have hdBound := hd.bound (half_pos hc)
  filter_upwards [hq0, hdBound, eventually_secondOrderScale_pos]
      with n hq0n hdn hscale
  have hdn' : |d n| <= (c / 2) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscale] using hdn
  have hdle : d n <= (c / 2) * secondOrderScale n :=
    (le_abs_self (d n)).trans hdn'
  calc
    (c / 2) * secondOrderScale n =
        c * secondOrderScale n -
          (c / 2) * secondOrderScale n := by ring
    _ <= q0 n - (c / 2) * secondOrderScale n :=
      sub_le_sub_right hq0n _
    _ <= q0 n - d n := sub_le_sub_left hdle _

/-- This is the paper's displayed implication: a base mass bounded below
on the `n / log n` scale and a change of order `n / log² n` yield a final
active mass with the required positive paper-scale lower bound. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =O[atTop]
      (fun n : Nat => secondOrderScale n / L n)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  apply bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    q0 d Hq0
  exact hd.trans_isLittleO
    secondOrderScale_div_L_isLittleO_secondOrderScale





/-! ## Literal scaled seeds and actual-measure constructors -/







/-! ## The literal paper-head specialization -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic -/
section


/-!
# The analytic Section 8 smooth-row quota and height bridge

The raw active smooth component from the exact companion file has a positive
`n / log n` lower bound by the repository's uniform de Bruijn--Saias and
fixed-head estimates.  This file proves that bound directly for complete-
rough label one, then propagates it through the exact nearest-integer and
height-center constructions.

Only one repository-level analytic ledger remains absent.  It is named
`BankPaperCanonicalSectionEightAnalyticLedger` below and contains exactly:

* the actual post-guard smooth mass differs from the explicit raw base mass
  by `o(n / log n)`;
* the literal frozen height defect `A0` is `O(n / log n)`.

These are precisely the two estimates asserted together in the paper's
Section 8 frozen ledger.  No selector, active-measure, or positivity premise
is hidden in that predicate.  Every consequence after it, including
`d = O(n / log^2 n)` and the positive lower bound for `q0 - d`, is proved
here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The label-one raw base pool is macroscopically large -/







/-- Therefore the literal `betaAct / L` base component has the minimal
positive paper-scale lower bound whenever `betaAct > 0`. -/
theorem bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c) (hbeta : 0 < betaAct) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct) := by
  use betaAct * roughCanonicalRawBroadPoolDensity W,
    mul_pos hbeta (roughCanonicalRawBroadPoolDensity_pos W)
  have hpool :=
    eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower W K hc
  filter_upwards [hpool, eventually_gt_atTop 1] with n hpoolN hn
  have hL : 0 < L n := L_pos hn
  calc
    (betaAct * roughCanonicalRawBroadPoolDensity W) * secondOrderScale n =
        (betaAct / L n) *
          (roughCanonicalRawBroadPoolDensity W * (n : Real)) := by
      unfold secondOrderScale L
      ring
    _ <= (betaAct / L n) *
          ((bankPaperCanonicalRawSmoothBasePool W n
            (upperTailLength c n) K).card : Real) :=
      mul_le_mul_of_nonneg_left hpoolN (div_nonneg hbeta.le hL.le)
    _ = bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) K betaAct := by
      rfl

/-- The raw base mass is also `O(n / log n)`, by the elementary containment
of its support in the broad interval. -/
theorem bankPaperCanonicalRawSmoothBaseMass_isBigO
    (W K : Nat) (c betaAct : Real) :
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct) =O[atTop] secondOrderScale := by
  apply (isBigO_iff).2
  use |betaAct|
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hscale : 0 < secondOrderScale n := secondOrderScale_pos (by omega)
  have hsubset : bankPaperCanonicalRawSmoothBasePool W n
      (upperTailLength c n) K ⊆
        roughBroadLowerBlock n (upperTailLength c n) K := by
    intro a ha
    change a ∈ roughCanonicalBroadCorrectionPool W n
      (upperTailLength c n) K (yNat n) 1 at ha
    have haRow := mem_completeRoughRowFiber.mp ha
    exact (mem_roughHeadFree.mp haRow.1).1
  have hcardNat :
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card <= n := by
    calc
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card <=
          (roughBroadLowerBlock n (upperTailLength c n) K).card :=
        Finset.card_le_card hsubset
      _ <= n := by
        simp only [roughBroadLowerBlock, Nat.card_Ioc]
        omega
  have hcard :
      ((bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card : Real) <= (n : Real) := by
    exact_mod_cast hcardNat
  have hcardNonneg :
      (0 : Real) <=
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) :=
    Nat.cast_nonneg _
  rw [bankPaperCanonicalRawSmoothBaseMass, Real.norm_eq_abs,
    abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hcardNonneg,
    Real.norm_eq_abs, abs_of_pos hscale]
  rw [secondOrderScale]
  have hcoef : 0 <= |betaAct| / L n :=
    div_nonneg (abs_nonneg _) hL.le
  calc
    |betaAct| / L n *
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) <=
        |betaAct| / L n * (n : Real) :=
      mul_le_mul_of_nonneg_left hcard hcoef
    _ = |betaAct| * ((n : Real) / L n) := by ring

/-! ## The exact missing analytic ledger -/



/-! ## Nearest-integer initialization preserves the paper scale -/

/-- The uniformly bounded initialization error is little-o of
`secondOrderScale`. -/
theorem bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
    (mFrozen qTilde : Nat -> Real) :
    (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
      qTilde n) =o[atTop] secondOrderScale := by
  have hbounded :
      (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        qTilde n) =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply (isBigO_iff).2
    use 1 / 2
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
        mFrozen qTilde n
  have hnorm : Tendsto (norm ∘ secondOrderScale) atTop atTop := by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using
      tendsto_abs_atTop_atTop.comp secondOrderScale_tendsto_atTop
  have hone : (fun _n : Nat => (1 : Real)) =o[atTop]
      secondOrderScale :=
    isLittleO_const_left.mpr (Or.inr hnorm)
  exact hbounded.trans_isLittleO hone

/-- A negligible raw-to-post-guard loss transfers the positive lower bound
from the explicit raw base mass to the actual mass `qTilde`. -/
theorem bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (rawBase qTilde : Nat -> Real)
    (Hraw : BankPaperCanonicalActiveMassPaperScaleLower rawBase)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower qTilde := by
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      rawBase (fun n => rawBase n - qTilde n) Hraw Hguard with
    ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring

/-- The half-unit nearest-integer initialization transfers that lower bound
from `qTilde` to the literal `q0` family. -/
theorem bankPaperCanonicalSmoothQ0Family_paperScaleLower
    (mFrozen qTilde : Nat -> Real)
    (HqTilde : BankPaperCanonicalActiveMassPaperScaleLower qTilde) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  have hd : (fun n => qTilde n -
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde n) =o[atTop]
        secondOrderScale :=
    hround.neg_left.congr_left (fun n => by ring)
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      qTilde
      (fun n => qTilde n -
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
      HqTilde hd with ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring

/-- A little-o raw-to-post-guard error also transfers the upper `O(N)`
bound. -/
theorem bankPaperCanonicalPostGuardSmoothMass_isBigO
    (rawBase qTilde : Nat -> Real)
    (Hraw : rawBase =O[atTop] secondOrderScale)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    qTilde =O[atTop] secondOrderScale := by
  exact (Hraw.sub Hguard.isBigO).congr_left (fun n => by ring)

/-- The nearest-integer `q0` family inherits the upper `O(N)` bound. -/
theorem bankPaperCanonicalSmoothQ0Family_isBigO
    (mFrozen qTilde : Nat -> Real)
    (HqTilde : qTilde =O[atTop] secondOrderScale) :
    bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
      secondOrderScale := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  exact (HqTilde.add hround.isBigO).congr_left (fun n => by ring)

/-! ## The logarithmically smaller height adjustment -/

/-- The paper's scale `n / log^2 n` tends to infinity. -/
theorem secondOrderScale_div_L_tendsto_atTop :
    Tendsto (fun n : Nat => secondOrderScale n / L n) atTop atTop := by
  have hzero : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa only [L, Function.comp_apply, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : Nat in atTop,
      0 < L n ^ 2 / (n : Real) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (pow_pos (L_pos hn) 2) (by positivity)
  have hright : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hnReal : (n : Real) ≠ 0 := by positivity
  apply (eq_div_iff hL.ne').2
  change (L n ^ 2 / (n : Real))⁻¹ * L n = (n : Real) / L n
  rw [inv_div]
  field_simp [hL.ne', hnReal]

/-- The reciprocal of `L + mu` is `O(1/L)` for fixed positive `mu`. -/
theorem bankPaperCanonical_inv_L_add_mu_isBigO_inv_L
    {mu : Real} (hmu : 0 < mu) :
    (fun n : Nat => (L n + mu)⁻¹) =O[atTop]
      (fun n : Nat => (L n)⁻¹) := by
  apply (isBigO_iff).2
  use 1
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hdenom : 0 < L n + mu := add_pos hL hmu
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdenom),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), one_mul]
  exact (inv_le_inv₀ hdenom hL).2 (le_add_of_nonneg_right hmu.le)

/-- From `q0 = O(N)` and `A0 = O(N)`, the exact rounded height adjustment
constructed in the companion file satisfies `d = O(N/L)`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_isBigO
    {mu : Real} (hmu : 0 < mu) (q0 A0 : Nat -> Real)
    (Hq0 : q0 =O[atTop] secondOrderScale)
    (HA0 : A0 =O[atTop] secondOrderScale) :
    (fun n => (bankPaperCanonicalSmoothHeightAdjustment
      n mu (q0 n) (A0 n) : Real)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
  have hnum : (fun n => mu * q0 n - A0 n) =O[atTop]
      secondOrderScale :=
    (Hq0.const_mul_left mu).sub HA0
  have hinv := bankPaperCanonical_inv_L_add_mu_isBigO_inv_L hmu
  have hcenter : (fun n => bankPaperCanonicalSmoothHeightCenter
      n mu (q0 n) (A0 n)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
    apply (hnum.mul hinv).congr
    · intro n
      rw [bankPaperCanonicalSmoothHeightCenter, div_eq_mul_inv]
    · intro n
      rw [div_eq_mul_inv]
  have hroundOne :
      (fun n => (bankPaperCanonicalSmoothHeightAdjustment
          n mu (q0 n) (A0 n) : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu (q0 n) (A0 n))
        =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply (isBigO_iff).2
    use 1 / 2
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
        n mu (q0 n) (A0 n)
  have hone : (fun _n : Nat => (1 : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
    apply (isBigO_iff).2
    use 1
    have hlarge := secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop (1 : Real))
    filter_upwards [hlarge] with n hn
    have hnonneg : 0 <= secondOrderScale n / L n := zero_le_one.trans hn
    simpa only [norm_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hnonneg] using hn
  have hround := hroundOne.trans hone
  exact (hcenter.add hround).congr_left (fun n => by ring)

/-! ## Full propagation from the minimal missing ledger -/

/-- Under the single missing Section 8 analytic ledger, the literal `q0`
family has a positive paper-scale lower bound. -/
theorem bankPaperCanonicalSectionEight_q0_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) := by
  have hraw := bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    W K hc hbeta
  have hpost := bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    qTilde hraw Hledger.1
  exact bankPaperCanonicalSmoothQ0Family_paperScaleLower
    mFrozen qTilde hpost

/-- The same ledger gives the paper's displayed `d = O(n/log^2 n)`. -/
theorem bankPaperCanonicalSectionEight_d_isBigO
    (W K : Nat) (c betaAct : Real) {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSmoothDRealFamily
        mu logY Lambda0 mFrozen qTilde =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  have hrawBigO := bankPaperCanonicalRawSmoothBaseMass_isBigO
    W K c betaAct
  have hpostBigO := bankPaperCanonicalPostGuardSmoothMass_isBigO
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    qTilde hrawBigO Hledger.1
  have hq0BigO := bankPaperCanonicalSmoothQ0Family_isBigO
    mFrozen qTilde hpostBigO
  simpa only [bankPaperCanonicalSmoothDRealFamily,
      bankPaperCanonicalSmoothDIntFamily] using
    bankPaperCanonicalSmoothHeightAdjustment_isBigO hmu
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)
      hq0BigO Hledger.2

/-- Consequently the constructed final active mass `qAct(d) = q0 - d`
retains a positive `n / log n` lower bound. -/
theorem bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde) := by
  have hq0 := bankPaperCanonicalSectionEight_q0_paperScaleLower
    W K hc hbeta logY Lambda0 mFrozen qTilde Hledger
  have hd := bankPaperCanonicalSectionEight_d_isBigO
    W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  exact bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
    (bankPaperCanonicalSmoothDRealFamily
      mu logY Lambda0 mFrozen qTilde) hq0 hd









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshSelectorProvider -/
section


/-!
# A placed-selector provider chosen before the final mesh

The placed-selector paper-rate theorem already chooses its uniform constant
before the regular relative mesh.  In the fixed-mesh Post-Hfit compositor,
however, its analytic `d`-bound and final-active-mass lower bound were
specialized only after a mesh had been supplied.

This file packages the same argument in the source-first parameter order.
The Section 8 ledger first selects one nonnegative `Cinitial`.  On one
common tail, and uniformly for every later mesh, the callback consumes only
the literal local source synchronizations, the alpha and beta boxes, the
nonempty correction pool, and exact synchronization of `d` and the fresh
bridge mass with their Section 8 families.  Its conclusion is exactly the
placed-selector deficit estimate; no Post-Hfit or terminal conclusion is
included.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## The literal mesh-uniform callback -/



/-! ## Selection from the Section 8 ledger -/

/-- Select one placed-selector constant from the exact Section 8 ledger,
strictly before any final regular mesh is introduced.

The proof intersects the uniform placed-selector event with the ledger's
`d = O(secondOrderScale / L)` estimate and positive paper-scale lower bound
for the final active mass.  Exact local family synchronization then supplies
the two numerical inequalities required by the underlying theorem. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct mu : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde))
    (hTwoW : 2 ≤ W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    (hc : 0 < c)
    (hdeltaStar : 0 < deltaStar)
    (hdeltaStarUpper : deltaStar < 1 / 18)
    (hbetaAct : 0 < betaAct)
    (hprefix : 2 * depth + 1 ≤ W)
    (hmu : 0 < mu) :
    ∃ Cinitial : Real, 0 ≤ Cinitial ∧
      BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
        Patterns I Cprom Cbank G (c := c) depth W K0
          deltaStar betaProt betaAct mu
          logY Lambda0 mFrozen qTilde Cinitial := by
  have hWone : 1 < W := by omega
  obtain ⟨Azero, hAzero, Nzero, Hzero⟩ :=
    exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate
      Patterns I Cprom Cbank G W hWone hHeadLe
  have HdBigO :=
    bankPaperCanonicalSectionEight_d_isBigO
      W (K0 + 1) c betaAct hmu
        logY Lambda0 mFrozen qTilde Hledger
  obtain ⟨Cd, hCd, Hd⟩ := (isBigO_iff').mp HdBigO
  rcases
      bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
        W (K0 + 1) hc hbetaAct hmu
          logY Lambda0 mFrozen qTilde Hledger with
    ⟨cFinal, hcFinal, HfinalMass⟩
  obtain ⟨Cinitial, hCinitial, Hselector⟩ :=
    exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate
      (betaProt := betaProt) (betaAct := betaAct)
      P Patterns I Cprom Cbank G W K0 depth hTwoW hHeadLe
        hc hdeltaStar hdeltaStarUpper (by norm_num : (0 : Real) < 1)
        hcFinal hAzero.le hCd.le hprefix
  refine ⟨Cinitial, hCinitial, ?_⟩
  unfold
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
  filter_upwards [
      Hselector, Hd, HfinalMass, eventually_ge_atTop Nzero]
      with n hselectorN hdN hfinalMassN hNzero
  intro delta eta M hmesh Bsource hBn hBW R certificate J S
    hbetaProtSync hbetaActSync hsep hremaining hcanonical hqTilde
    halpha hbetaBox hpool hdFamily hqFamily
  subst n
  have hscaleDiv :
      0 < secondOrderScale Bsource.sampleData.n /
        L Bsource.sampleData.n := by
    have hnOne : 1 < Bsource.sampleData.n := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        using J.postHeightBridge.n_gt_one
    exact div_pos (secondOrderScale_pos hnOne) (L_pos hnOne)
  have hdBound :
      |(J.d : Real)| ≤
        Cd *
          (secondOrderScale J.postHeightBridge.sampleData.n /
            J.postHeightBridge.L) := by
    have hdBoundN :
        |bankPaperCanonicalSmoothDRealFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n| ≤
          Cd * (secondOrderScale Bsource.sampleData.n /
            L Bsource.sampleData.n) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hscaleDiv] using hdN
    simpa only [
      hdFamily,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      BridgeData.L] using hdBoundN
  have hmass :
      cFinal *
          secondOrderScale J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.q := by
    rw [hqFamily]
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hfinalMassN
  have hzero :
      ∀ p : BandPrime J.postHeightBridge.sampleData.n
            J.postHeightBridge.sampleData.W,
        ∀ sign : PhysicalSign,
          (J.postHeightBridge.guardedCellProbability
              (none, sign)).expect
              (fun m ↦ valuation p.1 (m : Nat)) ≤
            Azero / (p.1 : Real) := by
    intro p sign
    exact
      Hzero J.postHeightBridge
        (by
          simpa only [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
            using hNzero)
        (by
          simpa only [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
            using hBW)
        hsep hremaining hcanonical p sign
  exact
    hselectorN M hmesh Bsource rfl hBW R certificate J S
      hbetaProtSync hbetaActSync hsep hremaining hcanonical hqTilde
      halpha hbetaBox hpool hdBound hmass hzero

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal005_003 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider
