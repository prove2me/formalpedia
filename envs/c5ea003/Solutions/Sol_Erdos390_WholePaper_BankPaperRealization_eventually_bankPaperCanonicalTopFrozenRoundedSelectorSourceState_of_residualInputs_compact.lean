-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.474143+00:00
-- url     : https://prove2.me/submissions/27324355-6f9b-415a-9bc1-31ee762f288c

import Definitions.Def_erdos390_remaining_analytic_propositions_004
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_qTildeSource
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass
import Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact


section
theorem Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower : Erdos390.RemainingAnalyticGoal008_004 := @Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact
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

/- Source module: Erdos390.WholePaper.CompleteRoughDecomposition -/
section


/-!
# Complete rough/smooth decomposition

The complete rough label retains exactly the prime-power coordinates above
`y`.  This file defines the complementary literal quotient and proves that
the two pieces recover the original natural number, with exact complementary
factorizations and no auxiliary decomposition hypothesis.
-/

namespace Erdos390.WholePaper

noncomputable section



/-! ## Positivity, divisibility, and product recovery -/





/-- Literal Finsupp form of the high-prime factorization. -/
theorem completeRoughLabel_factorization_eq_filter_gt (y a : ℕ) :
    (completeRoughLabel y a).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughSignature] using
    completeRoughLabel_factorization y a

/-- Coordinate form of the exact high-prime factorization. -/
theorem completeRoughLabel_factorization_apply (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeRoughLabel_factorization_eq_filter_gt y a)
  simpa only [Finsupp.filter_apply] using h







/-! ## The complementary low-prime factorization -/















/-! ## Uniqueness and the smooth-label criterion -/







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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger -/
section


/-!
# Guard-local canonical rough-row ledger

This module isolates the finite bookkeeping that occurs when the paper
passes from the raw canonical rough candidates to the candidates left after
the numerical guards

`Gamma_num = anchors ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Only literal finite-set identities are proved here.  In particular, this
file does **not** assume or assert a local guard census, a lower bound for a
guarded broad pool, or enough guarded-row capacity for a corrected selector.
Those still-missing estimates are exposed at the end as named propositions.

The postcharge target is kept in `Real` form for the correction algebra and
in `Int` form for its exact integrality witness.  Its nonnegativity is a
finite consequence of the actual donor/base row-preserving bijection and of
the disjoint upper-tail backing of the fixed exceptional factors and donors.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Literal guarded candidates and row pieces -/



























/-! ## The donor/base row-preserving bijection -/









/-! ## Upper-tail ownership and the postcharge target -/





/-- Every non-smooth row is either active nonexceptional or exceptional.
No asymptotic hypothesis is needed for this literal order dichotomy. -/
theorem roughCanonical_activeNonexceptional_or_exceptional
    {n label : ℕ} {deltaStar : ℝ} (hlabel : label ≠ 1) :
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ∨
      RoughCanonicalExceptionalLabel n deltaStar label := by
  by_cases hactive :
      (n : ℝ) ^ deltaStar ≤ 2 * (n : ℝ) / (label : ℝ)
  · exact Or.inl ⟨hlabel, hactive⟩
  · exact Or.inr (lt_of_not_ge hactive)















theorem roughCanonicalPostchargeRowTarget_eq_intCast
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (label : ℕ) :
    R.roughCanonicalPostchargeRowTarget deltaStar label =
      (R.roughCanonicalPostchargeRowTargetInt deltaStar label : ℝ) := by
  simp [roughCanonicalPostchargeRowTarget,
    roughCanonicalPostchargeRowTargetInt]







/-! ## Exact local discrepancy ledger -/







/-! ## Exact support reduction for the local deletion set -/







/-! ## Explicit remaining finite/analytic obligations -/







end BankPaperRealization

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

/- Source module: Erdos390.WholePaper.BankPaperProposition87ActualDataConnector -/
section


/-!
# Actual paper data at the Proposition 8.7 / guarded-selector interface

The paper does not use the mass-one normalization of the bridge.  Its
literal active weights are the numbers `z_m^0`, and

`q_n = sum_m z_m^0`.

At a clean numerical coordinate the protected frozen layer may overlap the
active layer.  Consequently `q_n` is not, in general, the sum of the whole
guarded selector on the active support.  This module keeps the two layers
separate.  Every guarded candidate is represented by a frozen tag of weight

`preSelector a - activeSeedAmbient a`,

while Proposition 8.7 evolves the active seed.  Thus the protected overlap
is retained exactly and the combined selector at time zero is the supplied
guarded pre-selector.

The single construction still missing from the finite guarded ledger is
named `BankPaperCanonicalActualActiveMeasureConstructor`.  It asks only for
the paper's active-measure realization: the seed has the canonical
barycentric shape, has eventual paper-scale mass at least one, is supported
on the guarded candidates, and is dominated by the already feasible
pre-selector.  Row integrality, target agreement, band balance, support,
pointwise estimates, and prefix estimates are not repeated in this
constructor; they are derived below from the existing guarded selector and
the Proposition 8.7 path.
-/

open Filter Topology Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The literal active mass and its sole construction socket -/

























/-! ## The actual scaled bridge data -/









/-! ## Tagged frozen remainder and exact push-forward -/





















/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/













/-! ## Smooth active support and unchanged complete-rough rows -/







/-- Push-forward mass over any finite set containing every active sample
value is the total tagged seed mass. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : ∀ m : D.Sample, D.value m ∈ support) :
    (∑ a ∈ support,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
    bankPaperCanonicalLiteralActiveMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim

/-- The active seed push-forward vanishes at a coordinate which is not the
value of any active sample tag. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) (ha : forall m : D.Sample, D.value m ≠ a) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg (ha m)]













/-! ## Prime support, exact bands, and the derived prefix ledger -/











/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



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



/-- A little-o raw-to-post-guard error also transfers the upper `O(N)`
bound. -/
theorem bankPaperCanonicalPostGuardSmoothMass_isBigO
    (rawBase qTilde : Nat -> Real)
    (Hraw : rawBase =O[atTop] secondOrderScale)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    qTilde =O[atTop] secondOrderScale := by
  exact (Hraw.sub Hguard.isBigO).congr_left (fun n => by ring)



/-! ## The logarithmically smaller height adjustment -/







/-! ## Full propagation from the minimal missing ledger -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement -/
section


/-!
# Paper-faithful placement boundary for the guarded smooth refinement

The smooth bridge in the paper does not preserve the medium-prime moments
of an earlier provisional selector.  It freezes the protected layer,
redistributes the active mass while preserving the smooth-row ledger and
the moments outside the tangent band, and then fits the medium-prime band
moments.  Proposition 8.7 supplies that latter fit.

Accordingly, the pre-selector part of the actual endpoint theorem needs
only complete-row integrality and deficit support outside the medium-prime
band.  Its older statement accepted a full rounded-selector tangent input,
although the proof used only those two fields.  This file records the
weaker exact theorem, constructs the minimized ledger from the paper's two
literal zero-head cells, and proves the exact scaled structured head-cell
moments.  It then resolves the support boundary--the nonzero head cells lie
in the smooth row, not in its head-free correction subpool--by transporting
a signed ledger over the whole smooth row for the corrected selector.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization



/-! ## Exact finite algebra for the two zero-head pools -/



/-- Uniform spreading realizes the requested cell mass exactly. -/
theorem sum_bankPaperCanonicalUniformCellIncrement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (cell : Cell Head)
    (mass : Real) :
    (∑ m : D.Sample,
      bankPaperCanonicalUniformCellIncrement D cell mass m) = mass := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single cell]
  · simp only [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, if_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (D.SampleAt cell) : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (D.sampleAt_card_pos cell)
    field_simp [hcard]
  · intro other _hother hne
    apply Finset.sum_eq_zero
    intro m _hm
    simp [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ cell)).elim



/-- The two zero-head pool changes alter the tagged active mass by exactly
the sum of their two requested masses. -/
theorem sum_bankPaperCanonicalTwoZeroHeadCellRebalance_sub
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real) :
    (∑ m : D.Sample,
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m - seed m)) = minusMass + plusMass := by
  calc
    (∑ m : D.Sample,
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m - seed m)) =
        (∑ m : D.Sample,
          bankPaperCanonicalUniformCellIncrement
            D (none, .minus) minusMass m) +
        ∑ m : D.Sample,
          bankPaperCanonicalUniformCellIncrement
            D (none, .plus) plusMass m := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalTwoZeroHeadCellRebalance
      ring
    _ = minusMass + plusMass := by
      rw [sum_bankPaperCanonicalUniformCellIncrement,
        sum_bankPaperCanonicalUniformCellIncrement]

/-- Literal active mass after the two pool changes. -/
theorem bankPaperCanonicalLiteralActiveMass_twoZeroHeadCellRebalance
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
          minusMass plusMass) =
      bankPaperCanonicalLiteralActiveMass D seed +
        minusMass + plusMass := by
  unfold bankPaperCanonicalLiteralActiveMass
  have hchange := sum_bankPaperCanonicalTwoZeroHeadCellRebalance_sub
    D seed minusMass plusMass
  rw [add_assoc, ← hchange]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

/-- For a canonical scaled seed, the preceding identity reads
`q + deltaMinus + deltaPlus` with no normalization surrogate. -/
theorem bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q minusMass plusMass : Real) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalTwoZeroHeadCellRebalance D
          (bankPaperCanonicalScaledActiveSeed T q)
          minusMass plusMass) = q + minusMass + plusMass := by
  rw [bankPaperCanonicalLiteralActiveMass_twoZeroHeadCellRebalance,
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]









/-! ## The head-free correction-pool ledger -/











/-! ## Structured head-cell realization -/





/-- Weighted ambient push-forward over a support containing all structured
values is exactly the corresponding tagged weighted sum. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : forall m : D.Sample, D.value m ∈ support)
    (p : Nat) :
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight D seed a *
          valuation p a) =
      ∑ m : D.Sample, seed m * valuation p (D.value m) := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim







/-- A uniform change in either physical copy of the zero head cell has
literally zero valuation moment at every prime represented in the head
simplex. -/
theorem sum_bankPaperCanonicalUniformZeroHeadCellIncrement_mul_valuation_eq_zero
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E)
    (sigma : PhysicalSign) (mass : Real)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : D.Sample,
        bankPaperCanonicalUniformCellIncrement D (none, sigma) mass m *
          valuation p.1 (D.value m)) = 0 := by
  apply Finset.sum_eq_zero
  intro m _hm
  by_cases hcell : D.cellOf m = (none, sigma)
  · have hpMem : p.1 ∈ (D.pattern (D.cellOf m).1).primes := by
      rw [hpattern]
      exact p.2
    have hmatch := D.value_matches_head m p.1 hpMem
    have hzero : (D.value m).factorization p.1 = 0 := by
      simpa [hpattern, hcell, PaperHeadSimplex.pattern] using hmatch
    rw [show valuation p.1 (D.value m) = 0 by
      simp [valuation, hzero]]
    ring
  · simp [bankPaperCanonicalUniformCellIncrement, hcell]

/-- Therefore both literal zero-head pool changes preserve every structured
head-prime moment exactly. -/
theorem sum_bankPaperCanonicalTwoZeroHeadCellRebalance_mul_valuation_eq
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : D.pattern = PaperHeadSimplex.pattern P hprime E)
    (seed : D.Sample -> Real) (minusMass plusMass : Real)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : D.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m * valuation p.1 (D.value m)) =
      ∑ m : D.Sample, seed m * valuation p.1 (D.value m) := by
  calc
    (∑ m : D.Sample,
        bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass m * valuation p.1 (D.value m)) =
      (∑ m : D.Sample, seed m * valuation p.1 (D.value m)) +
      (∑ m : D.Sample,
        bankPaperCanonicalUniformCellIncrement
            D (none, .minus) minusMass m *
          valuation p.1 (D.value m)) +
      ∑ m : D.Sample,
        bankPaperCanonicalUniformCellIncrement
            D (none, .plus) plusMass m *
          valuation p.1 (D.value m) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      unfold bankPaperCanonicalTwoZeroHeadCellRebalance
      ring
    _ = ∑ m : D.Sample, seed m * valuation p.1 (D.value m) := by
      rw [sum_bankPaperCanonicalUniformZeroHeadCellIncrement_mul_valuation_eq_zero
          D hprime E hpattern .minus minusMass p,
        sum_bankPaperCanonicalUniformZeroHeadCellIncrement_mul_valuation_eq_zero
          D hprime E hpattern .plus plusMass p]
      ring



/-! ## Exact support boundary -/



/-! ## Signed whole-smooth-row placement ledger -/



































end BankPaperRealization

/-! ## Weaker actual-endpoint preselector interface -/



namespace BankPaperRealization







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector -/
section


/-!
# Concrete producer and mass choice for the two zero-head cells

This file isolates the two finite facts needed by the structured
prebridge producer.

First, a sample in the zero head cell is coprime to the complete head
modulus.  Hence it belongs to the guarded broad correction pool as soon as
its physical interval lies below the literal broad cutoff and every sample
value is known pointwise to avoid the canonical guard set.  In particular, no
cardinality surplus theorem is used to prove membership.

Second, the height adjustment has a canonical symmetric realization: put
`-d / 2` in each of the two physical zero-head cells.  Its total change is
the integer `-d`, and the exact lower and upper coordinate-capacity
conditions reduce to two scalar inequalities involving the old total cell
mass and the guard-deleted cell cardinality.

The nearest-integer normalization from `qTilde` to `q0` is recorded
separately.  That first change is generally real rather than integral; the
integer prebridge ledger applies to the subsequent height change from
`q0` to `q0 - d`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums

noncomputable section

namespace BankPaperRealization

/-! ## The fixed physical intervals eventually lie below the broad cutoff -/

/-- A fixed endpoint strictly below `2` eventually leaves enough room for
the whole `K * upperTailLength` top strip.  This is the literal numerical
inequality used in the paper to put the upper physical pool below
`2n-Kh`. -/
theorem eventually_physicalBound_le_two_mul_sub_upperTailLength
    (K : Nat) {c b : Real} (hc : 0 < c) (hb0 : 0 <= b) (hbTwo : b < 2) :
    ∀ᶠ n : Nat in atTop,
      physicalBound b n <= 2 * n - K * upperTailLength c n := by
  have htailEvent : ∀ᶠ n : Nat in atTop,
      (((K * upperTailLength c n : Nat) : Real) / (n : Real)) < 2 - b := by
    have hT := (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
    have hzeroLt : (K : Real) * 0 < 2 - b := by
      simpa using sub_pos.mpr hbTwo
    have hsmall := hT.eventually
      (eventually_lt_nhds hzeroLt)
    filter_upwards [hsmall] with n hn
    have hn' :
        (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) < 2 - b := hn
    simpa [Nat.cast_mul, mul_div_assoc] using hn'
  filter_upwards [htailEvent, eventually_gt_atTop 0] with n htail hn
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have htailCross :
      ((K * upperTailLength c n : Nat) : Real) <
        (2 - b) * (n : Real) :=
    (div_lt_iff₀ hnReal).mp htail
  have hfloor :
      (physicalBound b n : Real) <= b * (n : Real) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hb0 (by positivity))
  have hsumReal :
      (physicalBound b n : Real) +
          (K * upperTailLength c n : Nat) < 2 * (n : Real) := by
    calc
      (physicalBound b n : Real) +
          (K * upperTailLength c n : Nat) <=
        b * (n : Real) + (K * upperTailLength c n : Nat) :=
          add_le_add hfloor le_rfl
      _ < 2 * (n : Real) := by nlinarith
  have hsumNat :
      physicalBound b n + K * upperTailLength c n <= 2 * n := by
    exact_mod_cast hsumReal.le
  omega

/-- Simultaneous two-sign form for the paper's fixed physical intervals. -/
theorem eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
    (I : PhysicalIntervals) (K : Nat) {c : Real} (hc : 0 < c)
    (hupperStrict : forall sigma, I.upper sigma < 2) :
    ∀ᶠ n : Nat in atTop, forall sigma,
      physicalBound (I.upper sigma) n <=
        2 * n - K * upperTailLength c n := by
  have hminus :=
    eventually_physicalBound_le_two_mul_sub_upperTailLength K hc
      (le_of_lt ((I.lower_pos .minus).trans (I.lower_lt_upper .minus)))
      (hupperStrict .minus)
  have hplus :=
    eventually_physicalBound_le_two_mul_sub_upperTailLength K hc
      (le_of_lt ((I.lower_pos .plus).trans (I.lower_lt_upper .plus)))
      (hupperStrict .plus)
  filter_upwards [hminus, hplus] with n hnMinus hnPlus
  intro sigma
  cases sigma with
  | minus => exact hnMinus
  | plus => exact hnPlus

/-! ## The zero head pattern produces head-freeness -/









/-! ## Canonical symmetric mass choices -/















/-! ## Exact finite coordinate capacity -/

/-- A symmetric change of arbitrary real total-cell mass has the expected
pointwise formula on either zero-head cell.  This is the common finite
algebra behind both the nearest-integer normalization and the integer
height adjustment. -/
theorem bankPaperCanonicalSymmetricRebalance_apply_of_zeroHeadCell
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (q mass : Real)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma)) :
    bankPaperCanonicalTwoZeroHeadCellRebalance D
        (bankPaperCanonicalScaledActiveSeed T q) mass mass m =
      (q * T.baseline.cellMass (none, sigma) + mass) /
        Fintype.card (D.SampleAt (none, sigma)) := by
  cases sigma <;>
    simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
      bankPaperCanonicalUniformCellIncrement,
      bankPaperCanonicalScaledActiveSeed,
      BaselineAllocation.baseWeight, hcell] <;>
    ring



/-- Pointwise form of the combined normalization-and-height change from
the actual post-guard mass `qTilde`. -/
theorem bankPaperCanonicalSymmetricInitialAndHeightRebalance_apply_of_zeroHeadCell
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (mFrozen qTilde : Real) (d : Int)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma)) :
    bankPaperCanonicalTwoZeroHeadCellRebalance D
        (bankPaperCanonicalScaledActiveSeed T qTilde)
        (bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d)
        (bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d) m =
      (qTilde * T.baseline.cellMass (none, sigma) +
          bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d) /
        Fintype.card (D.SampleAt (none, sigma)) := by
  exact bankPaperCanonicalSymmetricRebalance_apply_of_zeroHeadCell
    D T qTilde
      (bankPaperCanonicalSymmetricInitialAndHeightCellMass
        mFrozen qTilde d) m sigma hcell





/-- Exact removal criterion for the combined nearest-integer and height
change.  The displayed numerator is the final total mass assigned to this
one zero-head physical cell. -/
theorem bankPaperCanonicalSymmetricInitialAndHeightRebalance_nonneg_of_cellMass
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (T : BarycentricTarget D) (mFrozen qTilde : Real) (d : Int)
    (m : D.Sample) (sigma : PhysicalSign)
    (hcell : D.cellOf m = (none, sigma))
    (hremove : 0 <= qTilde * T.baseline.cellMass (none, sigma) +
      bankPaperCanonicalSymmetricInitialAndHeightCellMass
        mFrozen qTilde d) :
    0 <= bankPaperCanonicalTwoZeroHeadCellRebalance D
      (bankPaperCanonicalScaledActiveSeed T qTilde)
      (bankPaperCanonicalSymmetricInitialAndHeightCellMass
        mFrozen qTilde d)
      (bankPaperCanonicalSymmetricInitialAndHeightCellMass
        mFrozen qTilde d) m := by
  rw [bankPaperCanonicalSymmetricInitialAndHeightRebalance_apply_of_zeroHeadCell
    D T mFrozen qTilde d m sigma hcell]
  exact div_nonneg hremove (by positivity)

/-- Exact addition criterion for the same combined change.  Together with
the preceding theorem this is the literal finite `[0,1]` capacity problem
left to the Section 8 asymptotic estimates. -/
theorem bankPaperCanonicalSymmetricInitialAndHeightRebalance_protected_le_one_of_cellMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (T : BarycentricTarget B.sampleData)
    (mFrozen qTilde : Real) (d : Int) (betaProt : Real)
    (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma))
    (hadd : qTilde * T.baseline.cellMass (none, sigma) +
        bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d <=
      (Fintype.card (B.sampleData.SampleAt (none, sigma)) : Real) *
        (1 - betaProt / B.L)) :
    betaProt / B.L +
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T qTilde)
          (bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d)
          (bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d) m <= 1 := by
  rw [bankPaperCanonicalSymmetricInitialAndHeightRebalance_apply_of_zeroHeadCell
    B.sampleData T mFrozen qTilde d m sigma hcell]
  have hcard : 0 <
      (Fintype.card (B.sampleData.SampleAt (none, sigma)) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos (none, sigma)
  have hquot :
      (qTilde * T.baseline.cellMass (none, sigma) +
          bankPaperCanonicalSymmetricInitialAndHeightCellMass
            mFrozen qTilde d) /
          Fintype.card (B.sampleData.SampleAt (none, sigma)) <=
        1 - betaProt / B.L := by
    apply (div_le_iff₀ hcard).2
    simpa only [mul_comm] using hadd
  linarith

end BankPaperRealization

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenSourceConnector -/
section


/-!
# The frozen smooth-top source at the Section 8 initial stage

The paper's smooth-row initialization has three distinct layers:

* the `alpha`-weighted top block;
* the protected `betaProt / L` broad layer; and
* the structured active seed of total mass `qTilde`.

The older global corrected source retained the latter two layers on the
guarded broad pool, but its complete-label-one branch contained only the
ambient active seed.  In particular it did not contain the top block.

This connector defines a separate, finite `qTilde`-stage source which adds
that missing top layer.  On the guarded complete smooth row it is pointwise
equal to the literal raw weight with broad parameter `betaProt`, plus the
ambient old seed.  Consequently, when the old seed has total mass equal to
the guarded `betaAct` base mass, its whole guarded smooth-row sum is exactly
the balanced raw sum with broad parameter `betaProt + betaAct`.

No asymptotic estimate, post-height-fit displacement, or Section 9 source
state is asserted here.  The identities are finite and exact.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The missing smooth top layer -/







/-! ## Pointwise smooth-row identification -/





/-! ## Exact guarded-row mass identities -/

/-- Summing the pointwise bridge identifies the restored source mass with
the frozen raw mass plus the literal total mass of the old seed. -/
theorem sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_frozenRaw_add_activeMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a) =
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed := by
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
          (K := K) B R certificate oldSeed ha
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed := by
      rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
        B.sampleData oldSeed
          (R.roughCanonicalGuardedRow certificate deltaStar K 1)
            hvalues]









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector -/
section


/-!
# Nearest-integer source state for the frozen-top selector

The finite frozen-top source at mass `qTilde` has the paper's literal
smooth-row mass, but that mass need not be an integer.  The initialization
step replaces `qTilde` by

`q0 = nearestInteger(mFrozen + qTilde) - mFrozen`.

This connector proves the exact part of that handoff:

* changing the scaled seed from `qTilde` to `q0` changes no nonsmooth row;
* the new smooth-row total is the declared nearest integer;
* the charged nonsmooth-row equations therefore imply integrality of every
  complete rough row; and
* feasibility and exact target agreement outside the tangent prime band
  then package the result as `BankPaperCanonicalSelectorSourceState`.

The last two properties are retained as explicit premises.  They are not
consequences of row-mass rounding: feasibility is pointwise, while target
agreement is a prime-valuation identity.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The exact frozen mass and nearest-integer source -/







/-- Identification with the already audited combined
normalization-and-height cell mass at height `d = 0`.  This is the form
consumed by the existing zero-cell capacity estimates. -/
theorem bankPaperCanonicalTopFrozenNearestIntegerCellMass_eq_symmetricInitial
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha qTilde : Real) :
    bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde =
      bankPaperCanonicalSymmetricInitialAndHeightCellMass
        (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
          B R certificate deltaStar betaProt alpha)
        qTilde 0 := by
  unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
  unfold bankPaperCanonicalTopFrozenRoundedActiveMass
  unfold bankPaperCanonicalSymmetricInitialAndHeightCellMass
  unfold bankPaperCanonicalSmoothActiveMassAt
  norm_num





/-! ## Nonsmooth rows are independent of the active seed -/

/-- On every nonsmooth guarded row, changing the structured active seed is
pointwise invisible.  Active nonexceptional rows use the same corrected
weight for both seeds, while exceptional rows are zero for both seeds. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_eq_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha betaTotal : Real)
    (oldSeed₁ oldSeed₂ : B.sampleData.Sample -> Real) {a : Nat}
    (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed₁ a =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal oldSeed₂ a := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hlabel (haLabel.symm.trans haSmoothLabel)
  simp only [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, hnotSmoothPool,
    if_false, bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
    haLabel, hlabel]





/-- Replacing `qTilde` by `q0` is pointwise invisible on every nonsmooth
guarded row. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    {a : Nat} (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde a =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
  unfold bankPaperCanonicalTopFrozenRoundedSourceSelector
  exact
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_eq_of_mem_nonsmoothRow
      (K := K) B R certificate deltaStar betaProt alpha betaTotal
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalScaledActiveSeed T qTilde) hlabel ha

/-! ## Exact smooth and nonsmooth row ledgers -/

/-- The two zero-head corrections replace the literal active mass
`qTilde` by exactly `q0`. -/
theorem bankPaperCanonicalLiteralActiveMass_topFrozenRoundedActiveSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha qTilde : Real) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde) =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde := by
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  rw [bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed]
  unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
  ring

/-- The nearest-integer correction preserves every head-simplex valuation
moment because both increments are placed in the zero head cell. -/
theorem sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_headValuation_eq_qTilde
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha qTilde : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m *
          valuation p.1 (B.sampleData.value m)) =
      ∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T qTilde m *
          valuation p.1 (B.sampleData.value m) := by
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  exact
    sum_bankPaperCanonicalTwoZeroHeadCellRebalance_mul_valuation_eq
      B.sampleData hprime E hpattern
        (bankPaperCanonicalScaledActiveSeed T qTilde)
        (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
          B R certificate deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
          B R certificate deltaStar betaProt alpha qTilde)
        p

/-- Ambient form of the same head-moment preservation on any finite support
containing every structured active value. -/
theorem sum_bankPaperCanonicalTopFrozenRoundedAmbient_mul_headValuation_eq_qTilde
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha qTilde : Real)
    (support : Finset Nat)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈ support)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (p : {p : Nat // p ∈ P}) :
    (∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a *
          valuation p.1 a) =
      ∑ a ∈ support,
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde) a *
          valuation p.1 a := by
  rw [
    sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
      B.sampleData
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        support hvalues p.1,
    sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
      B.sampleData (bankPaperCanonicalScaledActiveSeed T qTilde)
        support hvalues p.1]
  exact
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_headValuation_eq_qTilde
      (K := K) B R certificate T deltaStar betaProt alpha qTilde
        hprime E hpattern p

/-- The rounded frozen-top smooth row has exactly the nearest-integer total
used to define `q0`. -/
theorem sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_smoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde a) =
      (bankPaperCanonicalSmoothInitialQuota
        (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
          B R certificate deltaStar betaProt alpha)
        qTilde : Real) := by
  have hsum :=
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_frozenRaw_add_activeMass
      (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
      (alpha := alpha) (beta := betaTotal) B R certificate
      (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
        B R certificate T deltaStar betaProt alpha qTilde)
      hvalues
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde a) =
        bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
            B R certificate deltaStar betaProt alpha +
          bankPaperCanonicalLiteralActiveMass B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) := by
      simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector,
        bankPaperCanonicalTopFrozenSmoothFrozenMass] using hsum
    _ = bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
          B R certificate deltaStar betaProt alpha +
        bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
          B R certificate deltaStar betaProt alpha qTilde := by
      rw [bankPaperCanonicalLiteralActiveMass_topFrozenRoundedActiveSeed]
    _ = (bankPaperCanonicalSmoothInitialQuota
          (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
            B R certificate deltaStar betaProt alpha)
          qTilde : Real) := by
      unfold bankPaperCanonicalTopFrozenRoundedActiveMass
      unfold bankPaperCanonicalSmoothInitialActiveMass
      ring

/-- The charged nonsmooth-row realization at `qTilde` transports unchanged
to the nearest-integer normalized source. -/
theorem bankPaperCanonicalChargedNonsmoothRowRealization_topFrozenRounded_of_qTilde
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde))) :
    BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  constructor
  · intro label hlabelMem hactive
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal
              qTilde a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact
            bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
              (K := K) B R certificate T deltaStar betaProt alpha
                betaTotal qTilde hactive.1 ha
      _ = R.roughCanonicalPostchargeRowTarget deltaStar label :=
        hrows.1 label hlabelMem hactive
  · intro label hlabelMem hlabel hexceptional
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal
              qTilde a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact
            bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
              (K := K) B R certificate T deltaStar betaProt alpha
                betaTotal qTilde hlabel ha
      _ = 0 := hrows.2 label hlabelMem hlabel hexceptional

/-! ## Exact feasibility transport through the two zero cells -/



/-! ## Complete-row integrality and the source-state handoff -/

/-- A selector with the charged nonsmooth row equations and one explicitly
integer smooth-row quota has integral mass in every complete rough row. -/
theorem bankPaperCanonicalSelectorRowIntegral_of_chargedNonsmoothRows_of_smoothQuota
    {c deltaStar : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (selector : Nat -> Real)
    (smoothQuota : Int)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar selector)
    (hsmooth :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        selector a) = (smoothQuota : Real)) :
    BankPaperCanonicalSelectorRowIntegral n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      selector := by
  intro label hlabelMem
  by_cases hlabel : label = 1
  · subst label
    refine ⟨smoothQuota, ?_⟩
    simpa only [BankPaperRealization.roughCanonicalGuardedRow] using hsmooth
  · rcases roughCanonical_activeNonexceptional_or_exceptional
      (n := n) (deltaStar := deltaStar) hlabel with
      hactive | hexceptional
    · refine
        ⟨R.roughCanonicalPostchargeRowTargetInt deltaStar label, ?_⟩
      have hrow := hrows.1 label hlabelMem hactive
      rw [R.roughCanonicalPostchargeRowTarget_eq_intCast
        deltaStar label] at hrow
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using hrow
    · refine ⟨0, ?_⟩
      have hrow := hrows.2 label hlabelMem hlabel hexceptional
      simpa only [BankPaperRealization.roughCanonicalGuardedRow,
        Int.cast_zero] using hrow

/-- Nearest-integer normalization internally supplies the complete-row
integrality field for the frozen-top source. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_rowIntegral
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde))) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  apply
    bankPaperCanonicalSelectorRowIntegral_of_chargedNonsmoothRows_of_smoothQuota
      R certificate
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde)
      (bankPaperCanonicalSmoothInitialQuota
        (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
          B R certificate deltaStar betaProt alpha)
        qTilde)
  · exact
      bankPaperCanonicalChargedNonsmoothRowRealization_topFrozenRounded_of_qTilde
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hrows
  · exact
      sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_smoothRow
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hvalues

/-- Exact `qTilde -> q0 -> SourceState` handoff.

Row integrality is now a conclusion.  The two remaining premises are
precisely the properties which nearest-integer row-mass normalization does
not imply: pointwise feasibility and selector-tail target agreement away
from the medium-prime band. -/
theorem bankPaperCanonicalTopFrozenRoundedSelectorSourceState
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K) R certificate deltaStar
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde)))
    (hfeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a ∧
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a <= 1)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde)) :
    BankPaperCanonicalSelectorSourceState (W := B.sampleData.W)
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  exact
    { feasible := hfeasible
      rowIntegral :=
        bankPaperCanonicalTopFrozenRoundedSourceSelector_rowIntegral
          (K := K) B R certificate T deltaStar betaProt alpha betaTotal
            qTilde hvalues hrows
      deficitSupportedOnPrimeBand := hsupport }

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateEventualConnector -/
section


/-!
# Eventual construction of the frozen-top rounded source state

The finite nearest-integer connector reduces the frozen-top source state to
three kinds of input:

* canonical sample geometry and the capacities of the two zero-head cells;
* feasibility of the literal `qTilde` source and its charged nonsmooth rows;
* exact selector-tail agreement outside the medium-prime band.

The first group is already asymptotic.  Canonical sample geometry is
provided by
`bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs`.  The
generic two-cell scalar-capacity theorem also supplies the initialization
capacity once it is applied to the uniformly bounded change
`(q0 - qTilde) / 2`.

This file packages that reuse.  The remaining residual input records only
the three facts for which the repository has no source-specific producer:
literal `qTilde` feasibility, charged nonsmooth rows, and literal `qTilde`
selector-tail support.  The zero-head correction is proved below to preserve
that support.  The equality identifying the analytic family `mFrozen` with
the concrete frozen-top row mass is also kept explicit at the eventual
synchronization boundary.
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

/-! ## The initial-only cell change and its capacity -/



/-- The nearest-integer change in one zero-head cell is little-o of the
paper active-mass scale. -/
theorem bankPaperCanonicalSymmetricInitialCellMassFamily_isLittleO
    (mFrozen qTilde : Nat -> Real) :
    bankPaperCanonicalSymmetricInitialCellMassFamily mFrozen qTilde
        =o[atTop]
      secondOrderScale := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  have hhalf := hround.const_mul_left ((1 : Real) / 2)
  exact hhalf.congr_left fun n => by
    unfold bankPaperCanonicalSymmetricInitialCellMassFamily
    unfold bankPaperCanonicalSymmetricInitialAndHeightCellMass
    unfold bankPaperCanonicalSmoothActiveMassAt
    unfold bankPaperCanonicalSmoothQ0Family
    ring

/-- The Section 8 analytic ledger supplies pointwise capacity for the
nearest-integer initialization itself.  Existing exported corollaries cover
height-only and combined initial-plus-height changes; this is the missing
`d = 0` specialization needed by the frozen-top source state. -/
theorem
    eventually_bankPaperCanonicalSymmetricInitial_twoZeroHeadCell_rebalance_capacity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (W K : Nat) {c betaAct marginFloor : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (hmarginFloor : 0 < marginFloor)
    (mFrozen qTilde A0 : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde A0)
    (betaProt : Real) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall (sigma : PhysicalSign)
              (m : B.sampleData.Sample),
              B.sampleData.cellOf m = (none, sigma) ->
              0 <=
                  bankPaperCanonicalTwoZeroHeadCellRebalance
                    B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T (qTilde n))
                    (bankPaperCanonicalSymmetricInitialCellMassFamily
                      mFrozen qTilde n)
                    (bankPaperCanonicalSymmetricInitialCellMassFamily
                      mFrozen qTilde n) m ∧
              betaProt / B.L +
                  bankPaperCanonicalTwoZeroHeadCellRebalance
                    B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T (qTilde n))
                    (bankPaperCanonicalSymmetricInitialCellMassFamily
                      mFrozen qTilde n)
                    (bankPaperCanonicalSymmetricInitialCellMassFamily
                      mFrozen qTilde n) m <= 1 := by
  let rawBase : Nat -> Real := fun n =>
    bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct
  have HrawLower :
      BankPaperCanonicalActiveMassPaperScaleLower rawBase := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
        W K hc hbeta
  have HqTildeLower :
      BankPaperCanonicalActiveMassPaperScaleLower qTilde :=
    bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
      rawBase qTilde HrawLower Hledger.1
  have HrawBigO : rawBase =O[atTop] secondOrderScale := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have HqTildeBigO : qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      rawBase qTilde HrawBigO Hledger.1
  have Hchange :
      bankPaperCanonicalSymmetricInitialCellMassFamily mFrozen qTilde
          =o[atTop]
        secondOrderScale :=
    bankPaperCanonicalSymmetricInitialCellMassFamily_isLittleO
      mFrozen qTilde
  have hcapacity :=
    eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass
      (P := P) (Band := Band)
      Phead I Cprom Cbank ledger qTilde
        (bankPaperCanonicalSymmetricInitialCellMassFamily mFrozen qTilde)
        HqTildeLower HqTildeBigO Hchange hmarginFloor betaProt
  filter_upwards [hcapacity] with n hcapacityN
  intro B hBn hsep hremaining hcanonical T hTmargin sigma m hcell
  have hscalar :=
    hcapacityN B hBn hsep hremaining hcanonical T hTmargin sigma
  exact
    ⟨bankPaperCanonicalSymmetricInitialAndHeightRebalance_nonneg_of_cellMass
        B.sampleData T (mFrozen n) (qTilde n) 0
          m sigma hcell hscalar.1,
      bankPaperCanonicalSymmetricInitialAndHeightRebalance_protected_le_one_of_cellMass
        B T (mFrozen n) (qTilde n) 0 betaProt
          m sigma hcell hscalar.2⟩

/-! ## Selector-tail support transport -/

/-- On the guarded candidate set, replacing `qTilde` by the nearest-integer
seed changes the frozen-top source by exactly the corresponding ambient seed
change.  On the smooth row the frozen raw layer cancels; on every nonsmooth
row both sources agree and both active ambient weights vanish. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {a : Nat}
    (ha : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K) :
    bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a -
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde) a -
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    rw [bankPaperCanonicalTopFrozenRoundedSourceSelector,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde)
          haSmooth,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        B R certificate (bankPaperCanonicalScaledActiveSeed T qTilde)
          haSmooth]
    ring
  · have haRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K
          (completeRoughLabel (yNat B.sampleData.n) a) := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩)
    have hsourceEq :=
      bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hlabel haRow
    have hnewZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      have hmLabel := (mem_completeRoughRowFiber.mp hmSmooth).2
      exact hlabel hmLabel
    have holdZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T qTilde) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      have hmSmooth :=
        hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      have hmLabel := (mem_completeRoughRowFiber.mp hmSmooth).2
      exact hlabel hmLabel
    rw [hsourceEq, hnewZero, holdZero]
    ring

/-- The nearest-integer zero-head correction preserves the complete
frozen-top source moment at every prime represented by the head simplex. -/
theorem
    sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_mul_headValuation_eq_qTilde
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (p : {p : Nat // p ∈ P}) :
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal qTilde a *
          valuation p.1 a) =
      ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a *
          valuation p.1 a := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro m
    exact (mem_completeRoughRowFiber.mp
      (hactiveSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩))).1
  have hambient :=
    sum_bankPaperCanonicalTopFrozenRoundedAmbient_mul_headValuation_eq_qTilde
      (K := K) B R certificate T deltaStar betaProt alpha qTilde
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        hvalues hprime E hpattern p
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate T deltaStar betaProt alpha betaTotal
                qTilde a *
            valuation p.1 a -
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
              B R certificate deltaStar betaProt alpha betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde) a *
            valuation p.1 a)) =
      ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde) a -
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T qTilde) a) *
            valuation p.1 a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← sub_mul,
        bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
          (K := K) B R certificate T deltaStar betaProt alpha betaTotal
            qTilde hactiveSmooth ha]
    _ =
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde) a *
            valuation p.1 a) -
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T qTilde) a *
            valuation p.1 a := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = 0 := by
      rw [hambient, sub_self]

/-- Above `y`, the rounded and literal `qTilde` frozen-top sources have the
same valuation moment: nonsmooth rows agree pointwise, while the complete
smooth row has zero valuation at such a prime. -/
theorem
    sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_mul_factorization_eq_qTilde_of_yNat_lt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (q : Nat) (hyq : yNat B.sampleData.n < q) :
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate T deltaStar betaProt alpha betaTotal qTilde a *
          (a.factorization q : Real)) =
      ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T qTilde) a *
          (a.factorization q : Real) := by
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have hfactorization : a.factorization q = 0 := by
      have hrough :
          (completeRoughLabel (yNat B.sampleData.n) a).factorization q =
            0 := by
        rw [hlabel]
        simp
      rw [completeRoughLabel_factorization_apply, if_pos hyq] at hrough
      exact hrough
    rw [hfactorization]
    ring
  · have haRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K
          (completeRoughLabel (yNat B.sampleData.n) a) := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩)
    rw [
      bankPaperCanonicalTopFrozenRoundedSourceSelector_eq_qTildeSource_of_mem_nonsmoothRow
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal
          qTilde hlabel haRow]

/-- The zero-head nearest-integer correction transports selector-tail
support from the literal `qTilde` frozen-top source to the rounded source. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_deficitSupportedOnPrimeBand_of_qTilde
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hsource : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))) :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  intro q hqPrime hqNotBand
  have hsum :
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate T deltaStar betaProt alpha betaTotal
                qTilde a *
            (a.factorization q : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
              B R certificate deltaStar betaProt alpha betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde) a *
            (a.factorization q : Real) := by
    by_cases hqHead : q <= B.sampleData.W
    · have hqMem : q ∈ primesUpTo B.sampleData.W :=
        mem_primesUpTo.mpr ⟨hqPrime, hqHead⟩
      let p : {p : Nat // p ∈ P} := ⟨q, hhead hqMem⟩
      simpa only [p, valuation] using
        (sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_mul_headValuation_eq_qTilde
          (K := K) B R certificate T deltaStar betaProt alpha betaTotal
            qTilde hactiveSmooth hprime E hpattern p)
    · have hWq : B.sampleData.W < q := Nat.lt_of_not_ge hqHead
      have hyq : yNat B.sampleData.n < q := by
        by_contra hnotY
        have hqy : q <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
        exact hqNotBand (mem_primeBand.mpr ⟨hqPrime, hWq, hqy⟩)
      exact
        sum_bankPaperCanonicalTopFrozenRoundedSourceSelector_mul_factorization_eq_qTilde_of_yNat_lt
          (K := K) B R certificate T deltaStar betaProt alpha betaTotal
            qTilde q hyq
  simpa only [bankPaperCanonicalSelectorValuationDeficit, hsum] using
    hsource q hqPrime hqNotBand

/-! ## Exact residual input -/



/-! ## Finite assembly -/

/-- Canonical geometry, two-cell initialization capacity, and the residual
source-specific inputs construct the exact nearest-integer source state. -/
theorem bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_qTildeSource
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hbetaProt : 0 <= betaProt)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hminus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hminusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde m <= 1)
    (hplusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha qTilde m <= 1)
    (Hresidual : BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
      (K := K) B R certificate fixed T deltaStar betaProt alpha betaTotal
        qTilde) :
    BankPaperCanonicalSelectorSourceState (W := B.sampleData.W)
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha betaTotal qTilde) := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    intro m
    exact hactiveSmooth
      (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  have hfeasible :=
    bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_qTildeSource
      (K := K) B R certificate T deltaStar betaProt alpha betaTotal
        qTilde hbetaProt hsep hactiveSmooth Hresidual.1 hminus hplus
        hminusCapacity hplusCapacity
  have hsupport :=
    bankPaperCanonicalTopFrozenRoundedSourceSelector_deficitSupportedOnPrimeBand_of_qTilde
      (K := K) B R certificate fixed T deltaStar betaProt alpha betaTotal
        qTilde hactiveSmooth hprime E hpattern hhead Hresidual.2.2
  exact
    bankPaperCanonicalTopFrozenRoundedSelectorSourceState
      (K := K) B R certificate fixed T deltaStar betaProt alpha betaTotal
        qTilde hvalues Hresidual.2.1 hfeasible hsupport

/-! ## Eventual canonical supplier -/

/-- The narrow eventual `qTilde -> q0 -> SourceState` supplier.

Canonical-data geometry and initial two-cell capacity are discharged
internally.  At the synchronized finite index, the caller supplies only:

* the equality between the analytic `mFrozen` family and the concrete
  frozen-top smooth mass; and
* `BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt`.

Those are precisely the source-specific identities not proved by the
current Section 8/9 eventual infrastructure. -/
theorem
    eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperStrict : forall sigma, I.upper sigma < 2)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct marginFloor deltaStar betaProt : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (hmarginFloor : 0 < marginFloor)
    (hbetaProt : 0 <= betaProt)
    (hhead : primesUpTo W ⊆ P)
    (mFrozen qTilde A0 : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde A0) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell (PaperHeadSimplex.pattern P hprime E) I
                B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                (PaperHeadSimplex.pattern P hprime E) I
                (ledger B.sampleData.n) hsep hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
              (R.centralChangedMarkers depth))
            (_hguardAgreement : BankPaperCanonicalBridgeGuardAgreement
              (ledger B.sampleData.n) R certificate deltaStar)
            (T : BarycentricTarget B.sampleData),
              marginFloor <= T.cellMassMargin ->
              forall (fixed : Finset Nat) (alpha betaTotal : Real),
                mFrozen n =
                    bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
                      B R certificate deltaStar betaProt alpha ->
                BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
                    (K := K) B R certificate fixed T deltaStar betaProt
                      alpha betaTotal (qTilde n) ->
                BankPaperCanonicalSelectorSourceState
                  (W := B.sampleData.W) R certificate fixed
                  (R.roughCanonicalGuardedCandidateSet certificate
                    deltaStar K)
                  (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
                    B R certificate T deltaStar betaProt alpha betaTotal
                      (qTilde n)) := by
  have hcapacity :=
    eventually_bankPaperCanonicalSymmetricInitial_twoZeroHeadCell_rebalance_capacity
      (P := P) (Band := Band)
      (PaperHeadSimplex.pattern P hprime E)
      I Cprom Cbank ledger W K hc hbeta hmarginFloor
        mFrozen qTilde A0 Hledger betaProt
  have hupperBroad :=
    eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
      I K hc hupperStrict
  have hKh := eventually_mul_upperTailLength_le_self K hc
  filter_upwards [hcapacity, hupperBroad, hKh] with
    n hcapacityN hupperBroadN hKhN
  intro B hBn hBW hsep hremaining hcanonical
    R certificate hguardAgreement T hTmargin
    fixed alpha betaTotal hmFrozen Hresidual
  have hheadB : primesUpTo B.sampleData.W ⊆ P := by
    simpa only [hBW] using hhead
  have hKhB :
      K * upperTailLength c B.sampleData.n <= B.sampleData.n := by
    simpa only [hBn] using hKhN
  have hupperBroadB : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n := by
    intro sigma
    simpa only [hBn] using hupperBroadN sigma
  have hupperTwo : forall sigma, I.upper sigma <= 2 :=
    fun sigma => (hupperStrict sigma).le
  have hpattern :
      B.sampleData.pattern =
        PaperHeadSimplex.pattern P hprime E := by
    calc
      B.sampleData.pattern =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).pattern :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.pattern)
          hcanonical
      _ = PaperHeadSimplex.pattern P hprime E :=
        canonicalSampleData_pattern
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining
  have hgeometry :=
    bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
      (P := P) (Band := Band) (c := c) (depth := depth) (K := K)
      hprime E hE I hlowerOne hupperTwo Cprom Cbank ledger
      B hheadB hsep hremaining hcanonical R certificate deltaStar
      hguardAgreement hKhB hupperBroadB
  have hcellMass :
      bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
          B R certificate deltaStar betaProt alpha (qTilde n) =
        bankPaperCanonicalSymmetricInitialCellMassFamily
          mFrozen qTilde n := by
    rw [
      bankPaperCanonicalTopFrozenNearestIntegerCellMass_eq_symmetricInitial,
      bankPaperCanonicalSymmetricInitialCellMassFamily,
      hmFrozen]
  have hminusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha (qTilde n) m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha (qTilde n) m <=
            1 := by
    intro m hm
    simpa only [bankPaperCanonicalTopFrozenRoundedActiveSeed,
      hcellMass] using
      (hcapacityN B hBn hsep hremaining hcanonical T hTmargin
        .minus m hm)
  have hplusCapacity : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha (qTilde n) m ∧
          betaProt / B.L +
              bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate T deltaStar betaProt alpha (qTilde n) m <=
            1 := by
    intro m hm
    simpa only [bankPaperCanonicalTopFrozenRoundedActiveSeed,
      hcellMass] using
      (hcapacityN B hBn hsep hremaining hcanonical T hTmargin
        .plus m hm)
  exact
    bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_qTildeSource
      (K := K) B R certificate fixed T deltaStar betaProt alpha betaTotal
        (qTilde n) hprime E hpattern hheadB
        hbetaProt hgeometry.1 hgeometry.2.1
        hgeometry.2.2.1 hgeometry.2.2.2
        hminusCapacity hplusCapacity Hresidual

end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal004_013.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs
