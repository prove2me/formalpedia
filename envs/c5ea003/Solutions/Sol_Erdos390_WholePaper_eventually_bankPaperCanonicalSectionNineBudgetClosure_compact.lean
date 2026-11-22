-- Prove2me | solution 1 for Erdos390.WholePaper.eventually_bankPaperCanonicalSectionNineBudgetClosure_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:31:32.009064+00:00
-- url     : https://prove2.me/submissions/f7fa0579-c0b9-4f78-9fca-1b746854c40c

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_eventually_canonicalDistributedSectionNineCleanListLower_absorbed_compact


section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed : Erdos390.RemainingAnalyticGoal004_015.{u_1} := @Erdos390.WholePaper.BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed_compact
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

/- Source module: Erdos390.Full.RegularMeshPrimeCutoffsEventually -/
section


/-!
# Eventual population of every explicit regular-mesh prime cell

For a fixed regular mesh, each positive logarithmic cell has fixed positive
width.  Its multiplicative size on the original prime scale therefore tends
to infinity.  This file proves the scale-separation hypotheses used by the
Bertrand construction automatically for all sufficiently large `n`, and
hence produces the arithmetic partition and interval certificate without a
mesh or prime-existence assumption.
-/

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel RegularRelativeMesh PositiveCellTransfer

theorem tendsto_y_atTop :
    Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
  unfold y
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
    tendsto_natCast_atTop_atTop





namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)









end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

end

/- Source module: Erdos390.Full.RegularMeshActualMomentBoundsEventually -/
section


/-!
# Eventual actual-prime moment bounds on the canonical regular mesh

This file discharges the `MomentReady` inputs of
`RegularMeshActualMomentBounds` from the unconditional prime number theorem
quadratures.  The endpoint family is the canonical family of floored powers
of `y`; no continuum mesh, prime-population, or moment estimate is assumed.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)



theorem tendsto_log_y_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (y n)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_y_atTop





































variable {n W : ℕ}
  (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper











end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs

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









/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

































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

/- Source module: Erdos390.WholePaper.CentralAnchorCutoff -/
section


/-!
# The fixed-prefix central-anchor cutoff

For a fixed prefix depth `R`, the paper splits the central prime blocks at
`n / (R + 1)`.  This file gives an explicit sufficient threshold for all
scale separations and then connects that literal cutoff directly to the
large-prime routing and central-anchor product APIs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







/-- At the explicit threshold, the cutoff is at least `4(R+1)`. -/
theorem four_mul_succ_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    4 * (R + 1) ≤ centralAnchorCutoff R n := by
  rw [centralAnchorCutoff, Nat.le_div_iff_mul_le (by omega)]
  simpa only [centralAnchorCutoffThreshold, pow_two, mul_assoc] using hn



/-- The explicit threshold also puts `2n` strictly below the cutoff square. -/
theorem two_mul_lt_centralAnchorCutoff_sq
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * n < (centralAnchorCutoff R n) ^ 2 := by
  let X := centralAnchorCutoff R n
  have hX : 4 * (R + 1) ≤ X := by
    simpa only [X] using four_mul_succ_le_centralAnchorCutoff hn
  have hXPos : 0 < X := by omega
  have hnUpper : n < (R + 1) * (X + 1) := by
    simpa only [X, centralAnchorCutoff] using
      Nat.lt_mul_div_succ n (by omega : 0 < R + 1)
  have hlinear : 2 * (R + 1) * (X + 1) ≤ X ^ 2 := by
    calc
      2 * (R + 1) * (X + 1) ≤ 2 * (R + 1) * (2 * X) := by
        exact Nat.mul_le_mul_left (2 * (R + 1)) (by omega)
      _ = (4 * (R + 1)) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right X hX
      _ = X ^ 2 := by ring
  calc
    2 * n < 2 * ((R + 1) * (X + 1)) :=
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
    _ = 2 * (R + 1) * (X + 1) := by ring
    _ ≤ X ^ 2 := hlinear







































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalBacking -/
section


/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section







namespace BankPaperRealization





theorem paperFixedExceptionalFactors_subset_upperBlock
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆ roughUpperBlock n h := by
  intro a ha
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
  exact (mem_paperExceptionalUpperFactors.mp ha.1).1

/-- Every fixed exceptional factor is a literal upper-tail occurrence. -/
theorem paperFixedExceptionalFactors_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  simpa only [roughUpperBlock, upperEndpoint] using
    R.paperFixedExceptionalFactors_subset_upperBlock deltaStar



















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankAnchorCollisionFree -/
section


/-!
# Collision freedom between the complete central anchors and the actual bank

The large-anchor branch recovers the common prime marker from the complete
rough factorization above `yNat`.  Once the marker is recovered, the guarded
central-cofactor certificate excludes the two incident state cores.

The residual branch uses the more rigid shape
`2^k * p^e`.  A bottom marker is already above the residual cutoff.  For an
ordinary marker, divisibility first forces the residual base prime to be the
marker; its marker valuation is then one, so cancellation would make the
ordinary state core a power of two, contrary to the path certificate.

Donor-only occurrences do not create an extra case: ordinary donors and the
two nonterminal bottom donors lie above `2n`, while terminal bottom donors
are literally their upper endpoint state.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The two eventual scale separations used by marker recovery -/

/-- The elementary square bound behind the separation
`yNat n < centralAnchorCutoff depth n`. -/
theorem bankAnchor_yNat_mul_self_le_self
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast





/-- At the literal central-anchor threshold, the moving smooth cutoff is
strictly below the residual/large-prime cutoff. -/
theorem yNat_lt_centralAnchorCutoff_of_threshold
    {depth n : ℕ} (hn : 1 ≤ n)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    yNat n < centralAnchorCutoff depth n := by
  have hySq := bankAnchor_yNat_mul_self_le_self hn
  have hcutSq := two_mul_lt_centralAnchorCutoff_sq hnCutoff
  nlinarith

theorem eventually_yNat_lt_centralAnchorCutoff (depth : ℕ) :
    ∀ᶠ n : ℕ in atTop, yNat n < centralAnchorCutoff depth n := by
  filter_upwards [eventually_ge_atTop 1,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth)]
      with n hn hnCutoff
  exact yNat_lt_centralAnchorCutoff_of_threshold hn hnCutoff

/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalDistributedTangentBridge -/
section


/-!
# Canonical selector boundary through a distributed tangent flow

This is the star-free replacement for the boundary portion of
`BankPaperCanonicalTangentResidualBridge`.  A distributed earthmover with
the literal canonical residual has the exact factorization boundary needed
by `tangentUpdate_valuation_eq_target`; equal request splitting preserves it.

No clean-list estimate or final collision conclusion occurs in this module.
The only collision-facing asymptotic recorded here is the unconditional
dense-support ceiling `yNat^3 / n -> 0`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Even the deliberately dense distributed support census is at most
`yNat n ^ 2` on the literal canonical prime band.  Consequently its
endpoint-weighted ceiling term is only cubic in `yNat n`. -/
theorem tangentDistributedSupportCount_canonical_le_yNat_sq
    {n W : Nat} :
    tangentDistributedSupportCount
        (BankPaperCanonicalTangentPrime n W) <= yNat n ^ 2 := by
  have hcard : (primeBand n W).card <= yNat n := by
    calc
      (primeBand n W).card <= (Finset.Icc 1 (yNat n)).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_Icc.mpr
          ⟨(prime_of_mem_primeBand hp).pos,
            le_yNat_of_mem_primeBand hp⟩
      _ = yNat n := by simp
  unfold tangentDistributedSupportCount
  rw [Fintype.card_coe]
  simpa only [pow_two] using Nat.mul_le_mul hcard hcard

/-- The cubic endpoint ceiling created by the deliberately dense support
still vanishes at the paper cutoff `yNat = floor (n^(2/9))`. -/
theorem tangentDistributed_yNat_cubed_div_self_tendsto_zero :
    Tendsto
      (fun n : Nat => (yNat n : Real) ^ 3 / (n : Real))
      atTop (nhds 0) := by
  have hmodel : Tendsto
      (fun n : Nat => (n : Real) ^ (-(1 / 3 : Real)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop
      (by norm_num : (0 : Real) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop
  apply squeeze_zero'
  · filter_upwards [] with n
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hyNonneg : 0 <= y n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hyFloor : (yNat n : Real) <= y n := Nat.floor_le hyNonneg
    have hyCube : (yNat n : Real) ^ 3 <= y n ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) hyFloor 3
    have hyPow : y n ^ 3 = (n : Real) ^ (2 / 3 : Real) := by
      calc
        y n ^ 3 = ((n : Real) ^ (2 / 9 : Real)) ^ 3 := rfl
        _ = (n : Real) ^ ((2 / 9 : Real) * (3 : Nat)) :=
          (Real.rpow_mul_natCast (Nat.cast_nonneg n)
            (2 / 9 : Real) 3).symm
        _ = (n : Real) ^ (2 / 3 : Real) := by norm_num
    calc
      (yNat n : Real) ^ 3 / (n : Real) <=
          y n ^ 3 / (n : Real) :=
        div_le_div_of_nonneg_right hyCube hnR.le
      _ = (n : Real) ^ ((2 / 3 : Real) - 1) := by
        rw [hyPow, Real.rpow_sub hnR, Real.rpow_one]
      _ = (n : Real) ^ (-(1 / 3 : Real)) := by norm_num
  · exact hmodel

/-- The canonical dense-support ceiling is bounded by the literal cubic
majorant before any limit is taken. -/
theorem tangentDistributedPaperCeilingBudget_canonical_le_yNat_cubic
    (n W : Nat) :
    tangentDistributedPaperCeilingBudget n (yNat n)
        (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W)) <=
      (4 + 2 * (yNat n : Real)) * (yNat n : Real) ^ 2 / (n : Real) := by
  have hsupport :
      (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W) : Real) <=
        (yNat n : Real) ^ 2 := by
    exact_mod_cast
      (tangentDistributedSupportCount_canonical_le_yNat_sq
        (n := n) (W := W))
  unfold tangentDistributedPaperCeilingBudget
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsupport (by positivity))
    (Nat.cast_nonneg n)

/-- Hence the exact canonical ceiling budget tends to zero for every fixed
head cutoff `W`; no prime-number estimate is used. -/
theorem tangentDistributedPaperCeilingBudget_canonical_tendsto_zero
    (W : Nat) :
    Tendsto
      (fun n : Nat =>
        tangentDistributedPaperCeilingBudget n (yNat n)
          (tangentDistributedSupportCount
            (BankPaperCanonicalTangentPrime n W)))
      atTop (nhds 0) := by
  have hsix : Tendsto
      (fun n : Nat => 6 * ((yNat n : Real) ^ 3 / (n : Real)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      tangentDistributed_yNat_cubed_div_self_tendsto_zero.const_mul 6
  apply squeeze_zero'
  · filter_upwards [] with n
    unfold tangentDistributedPaperCeilingBudget
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hyOneNat : 1 <= yNat n := by
      rw [yNat]
      apply Nat.le_floor
      rw [y]
      simpa only [Nat.cast_one] using
        Real.one_le_rpow
          (show (1 : Real) <= (n : Real) by
            exact_mod_cast (show 1 <= n by omega))
          (by norm_num : (0 : Real) <= 2 / 9)
    have hyOne : (1 : Real) <= yNat n := by exact_mod_cast hyOneNat
    have hySqLeCube : (yNat n : Real) ^ 2 <= (yNat n : Real) ^ 3 := by
      have hnonneg : 0 <= (yNat n : Real) ^ 2 := sq_nonneg _
      calc
        (yNat n : Real) ^ 2 = (yNat n : Real) ^ 2 * 1 := by ring
        _ <= (yNat n : Real) ^ 2 * (yNat n : Real) :=
          mul_le_mul_of_nonneg_left hyOne hnonneg
        _ = (yNat n : Real) ^ 3 := by ring
    calc
      tangentDistributedPaperCeilingBudget n (yNat n)
          (tangentDistributedSupportCount
            (BankPaperCanonicalTangentPrime n W)) <=
        (4 + 2 * (yNat n : Real)) * (yNat n : Real) ^ 2 /
          (n : Real) :=
        tangentDistributedPaperCeilingBudget_canonical_le_yNat_cubic n W
      _ <= 6 * (yNat n : Real) ^ 3 / (n : Real) := by
        apply div_le_div_of_nonneg_right _ hnR.le
        calc
          (4 + 2 * (yNat n : Real)) * (yNat n : Real) ^ 2 =
              4 * (yNat n : Real) ^ 2 +
                2 * (yNat n : Real) ^ 3 := by ring
          _ <= 4 * (yNat n : Real) ^ 3 +
                2 * (yNat n : Real) ^ 3 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hySqLeCube (by norm_num))
              (le_refl _)
          _ = 6 * (yNat n : Real) ^ 3 := by ring
      _ = 6 * ((yNat n : Real) ^ 3 / (n : Real)) := by ring
  · exact hsix

/-- The dense canonical support therefore satisfies the paper ceiling
smallness for every fixed positive density. -/
theorem eventually_tangentDistributedPaperCeilingBudget_canonical_le
    (W : Nat) {density : Real} (hdensity : 0 < density) :
    ∀ᶠ n : Nat in atTop,
      tangentDistributedPaperCeilingBudget n (yNat n)
          (tangentDistributedSupportCount
            (BankPaperCanonicalTangentPrime n W)) <=
        density ^ 2 / 96 := by
  exact
    (tangentDistributedPaperCeilingBudget_canonical_tendsto_zero W).eventually
      (eventually_le_nhds (by positivity : (0 : Real) < density ^ 2 / 96))



/-! ## Canonical notation for an arbitrary distributed flow -/

















/-! ## Selector bounds converted to the literal cell ledgers -/









/-! ## The explicit ratio-cell flow, rather than a supplied flow -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPaperCleanListAbsorption -/
section


/-!
# Closing the paper-scale tangent clean-list inequality

This file fixes the moving parameters used in Section 9 of the paper:

* `h = upperTailLength c n = ceil(c n / log n)`;
* `Phead = roughHeadModulus W`;
* `X0 = ceil(n ^ deltaStar)`;
* `y = yNat n = floor(n ^ (2/9))`;
* `W < v <= u <= y` and `u / v <= r0 < 3/2`.

For fixed `W`, `K`, `c`, `r0`, and `deltaStar`, the head-density gap is

`roughHeadDensity W * (2 - r0)`.

We reserve one sixteenth of that gap as the effective list density.  A
slightly conservative explicit version of the paper's one-time cutoff makes
the canonical Selberg main term at most one quarter of the gap.  The
Lambda-squared endpoint remainder and the sharp bank deletion census are
then `o(n/u)`, uniformly for `u <= yNat n`.  The fixed-modulus endpoint loss,
the natural floors and ceilings, and `K*h` are absorbed at the same scale.

Consequently the final candidate-floor-versus-loss inequality is proved
eventually; it is not retained as a premise of the paper-facing wrapper.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Literal Section 9 parameters -/







/-- The fixed-head gap is positive whenever the endpoint-ratio cap is below
two. -/
theorem tangentPaperHeadGap_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperHeadGap W r0 := by
  unfold tangentPaperHeadGap
  exact mul_pos (roughHeadDensity_pos W) (sub_pos.mpr hr0)

/-- The retained one-sixteenth clean-list density is positive under the same
ratio cap. -/
theorem tangentPaperCleanListDensity_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperCleanListDensity W r0 := by
  unfold tangentPaperCleanListDensity
  exact div_pos (tangentPaperHeadGap_pos W hr0) (by norm_num)











/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/





/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometry -/
section


/-!
# Canonical exponent bands and merged multiplicative ratio cells

This file supplies the elementary geometry missing between the canonical
regular exponent mesh and the explicit ratio-cell earthmover.

For a natural lower endpoint `A` and a fixed real `rho > 1`, the raw
multiplicative cutoffs are

`floor (A * rho ^ k)`.

The raw cell of a label is the first interval

`(floor (A * rho ^ k), floor (A * rho ^ (k+1))]`

which contains it.  In each canonical exponent band the final raw fragment
is merged into its predecessor.  Thus a merged cell contains at most two raw
cells, and adjacent merged cells span at most three powers of `rho`.  This is
the exact reason that the paper chooses `rho ^ 3 < r0`.

Everything in this module is finite and elementary.  The final section
isolates the one genuinely analytic input still needed for the earthmover:
prime occupancy of every full fixed-ratio interval.  No prime-distribution
statement is stored in the geometry construction.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PositiveCellTransfer
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Raw multiplicative cells -/











theorem label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) :
    label <= tangentMultiplicativeRatioCutoff lower rho
      (tangentMultiplicativeRawCellIndex lower label rho + 1) := by
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩]
  exact Nat.find_spec
    (exists_label_le_tangentMultiplicativeRatioCutoff_succ
      hlower hrho label)

theorem tangentMultiplicativeRatioCutoff_rawCell_lt_label
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hlabel : lower < label) :
    tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho) < label := by
  let H := exists_label_le_tangentMultiplicativeRatioCutoff_succ
    hlower hrho label
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩]
  by_cases hk : Nat.find H = 0
  · simpa only [hk, tangentMultiplicativeRatioCutoff_zero] using hlabel
  · have hkone : 1 <= Nat.find H := Nat.one_le_iff_ne_zero.mpr hk
    have hminimal := Nat.find_min H
      (m := Nat.find H - 1) (Nat.sub_one_lt hk)
    have hpred : Nat.find H - 1 + 1 = Nat.find H :=
      Nat.sub_add_cancel hkone
    rw [hpred] at hminimal
    exact Nat.lt_of_not_ge hminimal

theorem tangentMultiplicativeRawCellIndex_mono
    {lower x y : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hxy : x <= y) :
    tangentMultiplicativeRawCellIndex lower x rho <=
      tangentMultiplicativeRawCellIndex lower y rho := by
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩, dif_pos ⟨hlower, hrho⟩]
  apply Nat.find_min'
    (exists_label_le_tangentMultiplicativeRatioCutoff_succ
      hlower hrho x)
  exact hxy.trans
    (Nat.find_spec
      (exists_label_le_tangentMultiplicativeRatioCutoff_succ
        hlower hrho y))



theorem tangentMultiplicativeRawCell_real_lower_lt
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hlabel : lower < label) :
    (lower : Real) *
        rho ^ tangentMultiplicativeRawCellIndex lower label rho <
      (label : Real) := by
  have hnat := tangentMultiplicativeRatioCutoff_rawCell_lt_label
    hlower hrho hlabel
  exact (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg lower)
    (pow_nonneg (by linarith) _))).mp hnat

theorem tangentMultiplicativeRawCell_real_upper
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) :
    (label : Real) <= (lower : Real) *
      rho ^ (tangentMultiplicativeRawCellIndex lower label rho + 1) := by
  have hnat :=
    label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
      hlower hrho (label := label)
  have hcast : (label : Real) <=
      (tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho + 1) : Nat) := by
    exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le
    (mul_nonneg (Nat.cast_nonneg lower) (pow_nonneg (by linarith) _)))

/-! ## Merging the terminal fragment -/







theorem tangentMergedRatioCellIndex_le_raw
    (lastRaw raw : Nat) :
    tangentMergedRatioCellIndex lastRaw raw <= raw := by
  exact Nat.min_le_left _ _

theorem tangentMergedRatioCellIndex_eq_self
    {lastRaw raw : Nat} (hraw : raw <= tangentMergedRatioLastCell lastRaw) :
    tangentMergedRatioCellIndex lastRaw raw = raw := by
  exact Nat.min_eq_left hraw



theorem raw_le_tangentMergedRatioCellIndex_add_one
    {lastRaw raw : Nat} (hraw : raw <= lastRaw) :
    raw <= tangentMergedRatioCellIndex lastRaw raw + 1 := by
  by_cases hfull : raw <= lastRaw - 1
  · rw [tangentMergedRatioCellIndex_eq_self hfull]
    omega
  · have hcap : lastRaw - 1 <= raw := by omega
    unfold tangentMergedRatioCellIndex
    rw [Nat.min_eq_right hcap]
    omega



/-- Same or adjacent merged cells come from raw indices at distance at most
two.  The extra unit is precisely the possible terminal merge. -/
theorem rawCellIndices_within_two_of_merged_sameOrAdjacent
    {lastRaw a b : Nat} (ha : a <= lastRaw) (hb : b <= lastRaw)
    (hcell :
      tangentMergedRatioCellIndex lastRaw a =
          tangentMergedRatioCellIndex lastRaw b ∨
        tangentMergedRatioCellIndex lastRaw a + 1 =
          tangentMergedRatioCellIndex lastRaw b ∨
        tangentMergedRatioCellIndex lastRaw b + 1 =
          tangentMergedRatioCellIndex lastRaw a) :
    a <= b + 2 ∧ b <= a + 2 := by
  have haUpper := raw_le_tangentMergedRatioCellIndex_add_one ha
  have hbUpper := raw_le_tangentMergedRatioCellIndex_add_one hb
  have haLower := tangentMergedRatioCellIndex_le_raw lastRaw a
  have hbLower := tangentMergedRatioCellIndex_le_raw lastRaw b
  rcases hcell with hsame | hforward | hbackward <;> omega

/-- If two labels have raw indices at distance at most two in this
orientation, their ratio is strictly below `rho^3`. -/
theorem tangentMultiplicativeRawCell_ratio_lt_cube
    {lower x y : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho)
    (_hxLower : lower < x) (hyLower : lower < y)
    (hindex : tangentMultiplicativeRawCellIndex lower x rho <=
      tangentMultiplicativeRawCellIndex lower y rho + 2) :
    (x : Real) / (y : Real) < rho ^ 3 := by
  let ix := tangentMultiplicativeRawCellIndex lower x rho
  let iy := tangentMultiplicativeRawCellIndex lower y rho
  have hxUpper : (x : Real) <= (lower : Real) * rho ^ (ix + 1) := by
    simpa only [ix] using
      (tangentMultiplicativeRawCell_real_upper
        hlower hrho (label := x))
  have hyLowerReal : (lower : Real) * rho ^ iy < (y : Real) := by
    simpa only [iy] using
      (tangentMultiplicativeRawCell_real_lower_lt
        hlower hrho hyLower)
  have hpow : rho ^ (ix + 1) <= rho ^ (iy + 3) := by
    apply pow_le_pow_right₀ (by linarith)
    dsimp only [ix, iy]
    omega
  have hxToBoundary : (x : Real) <=
      (lower : Real) * rho ^ (iy + 3) :=
    hxUpper.trans
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg lower))
  have hrhoCubePos : 0 < rho ^ 3 := pow_pos (by linarith) _
  have hboundary : (lower : Real) * rho ^ (iy + 3) <
      (y : Real) * rho ^ 3 := by
    rw [show iy + 3 = iy + 3 by rfl, pow_add]
    simpa only [mul_assoc] using
      (mul_lt_mul_of_pos_right hyLowerReal hrhoCubePos)
  have hyPos : (0 : Real) < y := by
    exact_mod_cast (hlower.trans hyLower)
  rw [div_lt_iff₀ hyPos]
  calc
    (x : Real) <= (lower : Real) * rho ^ (iy + 3) := hxToBoundary
    _ < (y : Real) * rho ^ 3 := hboundary
    _ = rho ^ 3 * (y : Real) := mul_comm _ _

/-! ## The canonical paper exponent bands -/









theorem bankPaperCanonicalExponentBandOf_mem_interval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalExponentBandLower M n W
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) < p.1 ∧
      p.1 <= bankPaperCanonicalExponentBandUpper M n W
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
    M hdelta hn hW S
  have hp := (E.band_eq_iff p (P.band p)).mp rfl
  simpa only [P, E, bankPaperCanonicalExponentBandOf,
    bankPaperCanonicalExponentBandLower,
    bankPaperCanonicalExponentBandUpper,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using hp

theorem bankPaperCanonicalExponentBandLower_pos
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    0 < bankPaperCanonicalExponentBandLower M n W band := by
  have hcut :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).cutoff_le_lower band
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  simpa only [bankPaperCanonicalExponentBandLower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using
      hWpos.trans_le hcut









/-- Every raw prime cell lies before the raw terminal fragment. -/
theorem bankPaperCanonicalRawRatioCellIndex_le_lastRaw
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p <=
      bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  have hlower := bankPaperCanonicalExponentBandLower_pos
    M hdelta hn hW S band
  have hpUpper :=
    (bankPaperCanonicalExponentBandOf_mem_interval
      M hdelta hn hW S p).2
  exact tangentMultiplicativeRawCellIndex_mono
    hlower hrho hpUpper





/-- Same or adjacent canonical merged cells have label ratio below
`rho^3`. -/
theorem bankPaperCanonical_sameOrAdjacentRatioCell_ratio_lt_cube
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    {source target : BankPaperCanonicalTangentPrime n W}
    (hcell : TangentSameOrAdjacentRatioCell
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
      source target) :
    (((max (bankPaperCanonicalTangentPrimeLabel source)
          (bankPaperCanonicalTangentPrimeLabel target) : Nat) : Real) /
      ((min (bankPaperCanonicalTangentPrimeLabel source)
          (bankPaperCanonicalTangentPrimeLabel target) : Nat) : Real)) <
        rho ^ 3 := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S source
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let lastRaw := bankPaperCanonicalLastRawRatioCell M
    (n := n) (W := W) rho band
  let sourceRaw :=
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho source
  let targetRaw :=
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho target
  have hband : band =
      bankPaperCanonicalExponentBandOf M hdelta hn hW S target := hcell.1
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  have hsourceLower : lower < source.1 := by
    simpa only [band, lower] using
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S source).1
  have htargetLower : lower < target.1 := by
    have ht :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S target).1
    simpa only [lower, band, hband] using ht
  have hsourceRaw : sourceRaw <= lastRaw := by
    simpa only [sourceRaw, lastRaw, band] using
      bankPaperCanonicalRawRatioCellIndex_le_lastRaw
        M hdelta hn hW S rho hrho source
  have htargetRaw : targetRaw <= lastRaw := by
    have ht := bankPaperCanonicalRawRatioCellIndex_le_lastRaw
      M hdelta hn hW S rho hrho target
    simpa only [targetRaw, lastRaw, band, hband] using ht
  have hmerged :
      tangentMergedRatioCellIndex lastRaw sourceRaw =
          tangentMergedRatioCellIndex lastRaw targetRaw ∨
        tangentMergedRatioCellIndex lastRaw sourceRaw + 1 =
          tangentMergedRatioCellIndex lastRaw targetRaw ∨
        tangentMergedRatioCellIndex lastRaw targetRaw + 1 =
          tangentMergedRatioCellIndex lastRaw sourceRaw := by
    simpa only [bankPaperCanonicalRatioCellIndex, sourceRaw, targetRaw,
      lastRaw, band, hband] using hcell.2
  have hrawDistance :=
    rawCellIndices_within_two_of_merged_sameOrAdjacent
      hsourceRaw htargetRaw hmerged
  by_cases hlabels : source.1 <= target.1
  · change (((max source.1 target.1 : Nat) : Real) /
      ((min source.1 target.1 : Nat) : Real)) < rho ^ 3
    rw [max_eq_right hlabels, min_eq_left hlabels]
    apply tangentMultiplicativeRawCell_ratio_lt_cube
      hlower hrho htargetLower hsourceLower
    simpa only [sourceRaw, targetRaw,
      bankPaperCanonicalRawRatioCellIndex, lower, band, hband] using
      hrawDistance.2
  · have hreverse : target.1 <= source.1 := Nat.le_of_not_ge hlabels
    change (((max source.1 target.1 : Nat) : Real) /
      ((min source.1 target.1 : Nat) : Real)) < rho ^ 3
    rw [max_eq_left hreverse, min_eq_right hreverse]
    apply tangentMultiplicativeRawCell_ratio_lt_cube
      hlower hrho hsourceLower htargetLower
    simpa only [sourceRaw, targetRaw,
      bankPaperCanonicalRawRatioCellIndex, lower, band, hband] using
      hrawDistance.1

/-- Concrete constructor of the downstream fixed-ratio geometry predicate.
The only numerical fact used after the cell construction is
`rho^3 < r0`. -/
theorem bankPaperCanonical_tangentRatioCellGeometry
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0) :
    TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) r0 := by
  intro source target hcell
  exact (bankPaperCanonical_sameOrAdjacentRatioCell_ratio_lt_cube
    M hdelta hn hW S hrho hcell).trans hratio |>.le

/-! ## Exact analytic occupancy boundary -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellMomentTraffic -/
section


/-!
# Moment collapse of the canonical ratio-cell traffic

The endpoint-by-endpoint Mertens envelope is useful for pointwise ports,
but it is deliberately too wasteful for the sum over all cell cuts: its
uniform error is repeated once at every cut.  For total traffic one first
interchanges the two finite sums.  A vertex in cell `i` occurs in exactly
`i` strict tails, so the complete tail census is the first moment of the
literal cell index.

For the canonical multiplicative cells that index is at most

`(log y / log rho) * (t_p - t_lower)`.

The arithmetic moment bounds already proved for the canonical regular
mesh then give the paper-sized factor `delta + ratio`.  The only loss from
the natural floors is the explicit quantity `log 2 / log y`.

No new asymptotic or distribution hypothesis occurs in this file.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## The finite cut/tail interchange -/



/-! ## Logarithmic control of the concrete cell index -/





/-! ## The exact shifted-coordinate moment -/







/-! ## Canonical-mesh bound for the shifted moment -/









/-! ## Moment majorants for the complete traffic ledger -/











/-! ## Paper-scale scalar reduction -/







/-! ## Concrete geometry for the normalized pointwise port -/









/-! ## Scalar Mertens cancellation in one PNT-normalized port -/









/-! ## Collapse of the remaining band endpoint gap -/





/-! ## Uniform paper-scale port envelope -/







/-! ## Paper-scale scalar reduction for the incident ledger -/









/-- The incident error coefficient vanishes after all paper parameters are
fixed. -/
theorem tendsto_bankPaperCanonicalRatioCellIncidentErrorCoefficient_zero
    (W : Nat) (rho tangentConstant : Real) :
    Tendsto
      (fun n : Nat =>
        bankPaperCanonicalRatioCellIncidentErrorCoefficient
          W n rho tangentConstant)
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun n : Nat => tangentConstant / Real.log (y n))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      RegularMeshPrimeCutoffs.Mesh.tendsto_log_y_atTop
  have hconstant : Tendsto
      (fun _n : Nat =>
        1 + 2 * bankPaperCanonicalRatioCellPortConstant rho *
          (Real.log 2 +
            5 * fullReciprocalSumUniformConstant /
              Real.log (W : Real) ^ 2))
      atTop
      (nhds
        (1 + 2 * bankPaperCanonicalRatioCellPortConstant rho *
          (Real.log 2 +
            5 * fullReciprocalSumUniformConstant /
              Real.log (W : Real) ^ 2))) :=
    tendsto_const_nhds
  simpa only [bankPaperCanonicalRatioCellIncidentErrorCoefficient,
    zero_mul] using hbase.mul hconstant

/-! ## A manifestly vanishing upper coefficient for total traffic -/



/-- The exact scalar remainder is bounded by the manifestly vanishing
upper coefficient as soon as the floored top endpoint is at least two. -/
theorem bankPaperCanonical_ratioCellTrafficErrorCoefficient_le_upper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {W n : Nat} {rho tangentConstant : Real}
    (hn : 1 < n) (hWtwo : 2 <= W) (hyNatTwo : 2 <= yNat n)
    (hrho : 1 < rho)
    (htangent : 0 <= tangentConstant) :
    bankPaperCanonicalRatioCellTrafficErrorCoefficient
        M n W rho tangentConstant <=
      bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
        M W n rho tangentConstant := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hyNatPos : (0 : Real) < yNat n := by positivity
  have hyFloor : (yNat n : Real) <= y n := by
    exact Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hlogNat : 0 < Real.log (yNat n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hlogNatY :
      Real.log (yNat n : Real) <= Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hlogLogNatY :
      Real.log (Real.log (yNat n : Real)) <=
        Real.log (Real.log (y n)) :=
    Real.log_le_log hlogNat hlogNatY
  have hWlog : 0 < Real.log (W : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hglobal :
      Real.log (Real.log (yNat n : Real)) -
          Real.log (Real.log (W : Real)) +
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 3 <=
        Real.log (Real.log (y n)) +
          |Real.log (Real.log (W : Real))| +
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 3 := by
    have habs := neg_le_abs (Real.log (Real.log (W : Real)))
    linarith
  have hfactor : 0 <= tangentConstant / (2 * Real.log (y n)) :=
    div_nonneg htangent (mul_nonneg (by norm_num) hlogy.le)
  unfold bankPaperCanonicalRatioCellTrafficErrorCoefficient
    bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
  have hscaled := mul_le_mul_of_nonneg_left hglobal hfactor
  field_simp [hlogy.ne', hWlog.ne', hlogrho.ne'] at hscaled ⊢
  nlinarith

/-- The upper total-traffic error coefficient tends to zero for every fixed
mesh, cutoff, ratio, and tangent constant. -/
theorem tendsto_bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient_zero
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W : Nat) (rho tangentConstant : Real) :
    Tendsto
      (fun n : Nat =>
        bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
          M W n rho tangentConstant)
      atTop (nhds 0) := by
  have hLTop : Tendsto (fun n : Nat => Real.log (y n)) atTop atTop :=
    RegularMeshPrimeCutoffs.Mesh.tendsto_log_y_atTop
  have hlogRatio : Tendsto
      (fun n : Nat =>
        Real.log (Real.log (y n)) / Real.log (y n))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hInv : Tendsto (fun n : Nat => 1 / Real.log (y n))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLTop
  have hfirst : Tendsto
      (fun n : Nat =>
        (tangentConstant / 2) *
          (Real.log (Real.log (y n)) / Real.log (y n)))
      atTop (nhds ((tangentConstant / 2) * 0)) :=
    tendsto_const_nhds.mul hlogRatio
  have hsecond : Tendsto
      (fun n : Nat =>
        (tangentConstant / 2 *
          (|Real.log (Real.log (W : Real))| +
            5 * fullReciprocalSumUniformConstant /
              Real.log (W : Real) ^ 3)) *
          (1 / Real.log (y n)))
      atTop
        (nhds
          ((tangentConstant / 2 *
            (|Real.log (Real.log (W : Real))| +
              5 * fullReciprocalSumUniformConstant /
                Real.log (W : Real) ^ 3)) * 0)) :=
    tendsto_const_nhds.mul hInv
  have hthird : Tendsto
      (fun n : Nat =>
        (6 * tangentConstant * M.ratio * (M.cellCount : Real) * Real.log 2 /
            Real.log rho) *
          (1 / Real.log (y n)))
      atTop
        (nhds
          ((6 * tangentConstant * M.ratio * (M.cellCount : Real) * Real.log 2 /
              Real.log rho) * 0)) :=
    tendsto_const_nhds.mul hInv
  simpa only [bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient,
    mul_zero, zero_add] using (hfirst.add hsecond).add hthird

/-- The floored paper endpoint tends to infinity. -/
theorem bankPaperCanonical_yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : Nat => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

/-- Once the fixed parameters have been chosen, both displayed scalar
remainders are eventually below arbitrary positive traffic and incident
error budgets. -/
theorem eventually_bankPaperCanonical_ratioCellErrorCoefficients_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W : Nat) (rho tangentConstant trafficError incidentError : Real)
    (htrafficError : 0 < trafficError)
    (hincidentError : 0 < incidentError) :
    ∀ᶠ n : Nat in atTop,
      2 <= yNat n ∧
      bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
          M W n rho tangentConstant <= trafficError ∧
      bankPaperCanonicalRatioCellIncidentErrorCoefficient
          W n rho tangentConstant <= incidentError := by
  have hyNat : ∀ᶠ n : Nat in atTop, 2 <= yNat n :=
    bankPaperCanonical_yNat_tendsto_atTop.eventually
      (eventually_ge_atTop 2)
  have htraffic :=
    (tendsto_bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient_zero
      M W rho tangentConstant).eventually
        (eventually_le_nhds htrafficError)
  have hincident :=
    (tendsto_bankPaperCanonicalRatioCellIncidentErrorCoefficient_zero
      W rho tangentConstant).eventually
        (eventually_le_nhds hincidentError)
  filter_upwards [hyNat, htraffic, hincident] with n hn hT hI
  exact ⟨hn, hT, hI⟩

/-! ## Explicit fixed choices for the paper budgets -/



/-- The fixed main-budget coefficient is positive for every `rho > 1`. -/
theorem bankPaperCanonical_ratioCellMainCoefficient_pos
    {rho : Real} (hrho : 1 < rho) :
    0 < bankPaperCanonicalRatioCellMainCoefficient rho := by
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hrho0 : 0 < rho := lt_trans zero_lt_one hrho
  have hrhoGap : 0 < rho - 1 := sub_pos.mpr hrho
  unfold bankPaperCanonicalRatioCellMainCoefficient
    bankPaperCanonicalRatioCellTrafficConstant
    bankPaperCanonicalRatioCellIncidentConstant
  exact add_pos
    (mul_pos (by norm_num) (div_pos (by norm_num) hlogrho))
    (mul_pos (by norm_num)
      (div_pos (mul_pos (by norm_num) (sq_pos_of_pos hrho0)) hrhoGap))





/-- At the displayed width choice, the main budget is exactly half of its
allowed `density^2 / 48` allocation. -/
theorem bankPaperCanonical_paperMainBudget_widthChoice_eq
    {density sigma rho tangentConstant : Real}
    (hsigma : 0 < sigma) (hrho : 1 < rho)
    (htangent : 0 < tangentConstant) :
    tangentDistributedPaperMainBudget
        (bankPaperCanonicalRatioCellTrafficConstant rho)
        (bankPaperCanonicalRatioCellIncidentConstant rho)
        tangentConstant
        (bankPaperCanonicalRatioCellPaperWidthChoice
          density sigma rho tangentConstant)
        sigma =
      density ^ 2 / 96 := by
  have hcoefficient :
      bankPaperCanonicalRatioCellMainCoefficient rho ≠ 0 :=
    (bankPaperCanonical_ratioCellMainCoefficient_pos hrho).ne'
  change
    (bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant *
        bankPaperCanonicalRatioCellPaperWidthChoice
          density sigma rho tangentConstant) / sigma =
      density ^ 2 / 96
  unfold bankPaperCanonicalRatioCellPaperWidthChoice
  field_simp [hcoefficient, htangent.ne', hsigma.ne']

/-- Any mesh width below the fixed choice satisfies the exact `hmain`
premise used by the Section 9 assembly. -/
theorem bankPaperCanonical_paperMainBudget_le
    {density sigma rho tangentConstant width : Real}
    (hsigma : 0 < sigma) (hrho : 1 < rho)
    (htangent : 0 < tangentConstant)
    (hwidth : width <= bankPaperCanonicalRatioCellPaperWidthChoice
      density sigma rho tangentConstant) :
    tangentDistributedPaperMainBudget
        (bankPaperCanonicalRatioCellTrafficConstant rho)
        (bankPaperCanonicalRatioCellIncidentConstant rho)
        tangentConstant width sigma <=
      density ^ 2 / 48 := by
  have hcoefficient :
      0 <= bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant :=
    mul_nonneg
      (bankPaperCanonical_ratioCellMainCoefficient_pos hrho).le htangent.le
  have hscaled := mul_le_mul_of_nonneg_left hwidth hcoefficient
  have hbudget :
      tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant width sigma <=
        tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant
          (bankPaperCanonicalRatioCellPaperWidthChoice
            density sigma rho tangentConstant)
          sigma := by
    change
      (bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant *
          width) / sigma <=
        (bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant *
          bankPaperCanonicalRatioCellPaperWidthChoice
            density sigma rho tangentConstant) / sigma
    exact div_le_div_of_nonneg_right hscaled hsigma.le
  calc
    tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant width sigma <=
        tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant
          (bankPaperCanonicalRatioCellPaperWidthChoice
            density sigma rho tangentConstant)
          sigma := hbudget
    _ = density ^ 2 / 96 :=
      bankPaperCanonical_paperMainBudget_widthChoice_eq
        hsigma hrho htangent
    _ <= density ^ 2 / 48 := by nlinarith [sq_nonneg density]



/-- The symmetric error allocation is positive for positive density and
split scale. -/
theorem bankPaperCanonical_ratioCellPaperErrorChoice_pos
    {density sigma : Real} (hdensity : 0 < density) (hsigma : 0 < sigma) :
    0 < bankPaperCanonicalRatioCellPaperErrorChoice density sigma := by
  unfold bankPaperCanonicalRatioCellPaperErrorChoice
  positivity

/-- Using the symmetric allocation for both errors exactly fills the
`density^2 / 96` paper error budget. -/
theorem bankPaperCanonical_paperErrorBudget_choice_eq
    {density sigma : Real} (hsigma : 0 < sigma) :
    tangentDistributedPaperErrorBudget
        (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
        (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
        sigma =
      density ^ 2 / 96 := by
  unfold tangentDistributedPaperErrorBudget
    bankPaperCanonicalRatioCellPaperErrorChoice
  field_simp [hsigma.ne']; ring

/-- For the explicit fixed error allocation, the asymptotic traffic and
incident coefficients jointly satisfy the precise `herror` premise of the
Section 9 assembly. -/
theorem eventually_bankPaperCanonical_paperErrorBudget_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W : Nat) (rho tangentConstant density sigma : Real)
    (hdensity : 0 < density) (hsigma : 0 < sigma) :
    ∀ᶠ n : Nat in atTop,
      2 <= yNat n ∧
      tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
            M W n rho tangentConstant)
          (bankPaperCanonicalRatioCellIncidentErrorCoefficient
            W n rho tangentConstant)
          sigma <= density ^ 2 / 96 := by
  have hchoice :
      0 < bankPaperCanonicalRatioCellPaperErrorChoice density sigma :=
    bankPaperCanonical_ratioCellPaperErrorChoice_pos hdensity hsigma
  have hcoefficients :=
    eventually_bankPaperCanonical_ratioCellErrorCoefficients_le
      M W rho tangentConstant
      (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
      (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
      hchoice hchoice
  filter_upwards [hcoefficients] with n hn
  refine ⟨hn.1, ?_⟩
  have htraffic := mul_le_mul_of_nonneg_left hn.2.1 (by norm_num :
    (0 : Real) <= 16)
  have hincident := mul_le_mul_of_nonneg_left hn.2.2 (by norm_num :
    (0 : Real) <= 8)
  have hbudget :
      tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
            M W n rho tangentConstant)
          (bankPaperCanonicalRatioCellIncidentErrorCoefficient
            W n rho tangentConstant)
          sigma <=
        tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
          (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
          sigma := by
    unfold tangentDistributedPaperErrorBudget
    exact div_le_div_of_nonneg_right
      (add_le_add htraffic hincident) hsigma.le
  exact hbudget.trans_eq
    (bankPaperCanonical_paperErrorBudget_choice_eq hsigma)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualP87RatioCellTrafficConnector -/
section


/-!
# Actual Proposition 8.7 residuals in the canonical ratio-cell traffic ledger

The actual Proposition 8.7 endpoint has primewise residual bound

`Cpost * q / (p * B.L)`,

where `q = B.q` is the literal active mass.  This file connects that bound to
the audited canonical ratio-cell moment and port estimates.  In particular,
the traffic scale below is always the literal

`Cpost * B.q / B.L`;

the active mass is never replaced by `1`.

There are two levels of output.

* The finite connector gives the weighted-residual, uniform-port, and total
  moment-traffic bounds at the actual scale, for the literal canonical
  partition.
* The paper-budget connector gives the scalar Section 9 main/error form after
  receiving the precise scale domination

  `Cpost * B.q / B.L <= tangentConstant * N / log y`.

The latter comparison is not manufactured here.  A reusable normalization
lemma shows that it follows from the equivalent numerator comparison after
using the exact identity `log y = (2/9) B.L`.

Finally, the eventual connector consumes the actual `MomentReady` producer.
It is uniform in the scale-separation proof and in every residual satisfying
the displayed balance and actual-scale pointwise hypotheses.  The quantitative
Mertens and fixed-ratio PNT hypotheses remain visible traffic inputs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Exact comparison of the actual P87 and harmonic pointwise forms -/





/-- Exact normalized criterion for domination by a Section 9 paper scale.

Since `log y = (2/9) B.L`, the numerator comparison

`(2/9) * (Cpost * q) <= tangentConstant * N`

implies the required comparison of the two pointwise scales. -/
theorem bankPaperCanonical_actualP87Scale_le_paperScale_of_normalized
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {Cpost tangentConstant N : Real}
    (hnormalized :
      (2 / 9 : Real) * (Cpost * B.q) <= tangentConstant * N) :
    Cpost * B.q / B.L <=
      tangentConstant * N / Real.log (y B.sampleData.n) := by
  have hlog :
      Real.log (y B.sampleData.n) = (2 / 9 : Real) * B.L := by
    calc
      Real.log (y B.sampleData.n) =
          (2 / 9 : Real) * Erdos390.Full.Scale.L B.sampleData.n :=
        Erdos390.Full.Scale.log_y
          (Nat.zero_lt_of_lt B.n_gt_one)
      _ = (2 / 9 : Real) * B.L := by
        rfl
  rw [hlog]
  have hL : 0 < B.L := B.L_pos
  have hden : 0 < (2 / 9 : Real) * B.L :=
    mul_pos (by norm_num) hL
  apply (div_le_div_iff₀ hL hden).2
  have hmul := mul_le_mul_of_nonneg_right hnormalized hL.le
  calc
    Cpost * B.q * ((2 / 9 : Real) * B.L) =
        ((2 / 9 : Real) * (Cpost * B.q)) * B.L := by ring
    _ <= (tangentConstant * N) * B.L := hmul

/-! ## The common finite traffic payload -/



/-! ## Selector-facing actual-P87 traffic -/



/-! ## Assembly-facing paper main/error form -/



/-! ## Eventual actual-scale moment traffic -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNineBudgetClosure -/
section


/-!
# Canonical Section 9 budget closure

This connector discharges the three literal clean-list hypotheses and the
three scalar paper budgets left visible by the final Section 9 geometry
theorem.  It also turns one narrow upper estimate for the actual
Proposition 8.7 mass,

`q_n <= Cq * secondOrderScale n`,

into the exact paper-scale domination used by that theorem.

The clean density is the canonical
`tangentPaperCleanListDensity W r0`.  The main budget is finite once the
mesh width is below its explicit choice; the error and ceiling budgets are
eventual consequences of the canonical ratio-cell estimates.  The only new
analytic input is the displayed upper estimate for `q_n`, together with its
fixed scalar coefficient comparison.

The existing parameter-synchronization theorem supplies the fixed
`depth`, `W`, and `r0` facts consumed by the closure; a projection below
records this interface explicitly.  For the clean triplet we use its
distributed clean-list adapter.  That adapter reindexes the same absorbed
clean-list terminal to the literal ratio-cell earthmover, whereas the older
star-flow Section 9 absorbed wrapper has the wrong flow type here.

The Post-Hfit nonsmooth slack package is deliberately not repeated here.
It is an independent finite premise of the final geometry connector, while
the estimates below depend only on clean-list absorption, canonical cell
geometry, and scalar asymptotics.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Synchronized core parameters -/



/-! ## Exact logarithmic and actual-mass reductions -/

/-- The literal bridge logarithm cancels the second-order denominator once
the bridge sample index is synchronized with the ambient index. -/
theorem bankPaperCanonical_bridgeL_mul_secondOrderScale_eq
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {n : Nat}
    (hBn : B.sampleData.n = n) :
    B.L * secondOrderScale n = (n : Real) := by
  subst n
  change
    Real.log (B.sampleData.n : Real) *
        ((B.sampleData.n : Real) /
          Real.log (B.sampleData.n : Real)) =
      (B.sampleData.n : Real)
  have hlog : Real.log (B.sampleData.n : Real) ≠ 0 := by
    simpa only [BridgeData.L] using B.L_pos.ne'
  field_simp [hlog]

/-- A pointwise actual-P87 mass upper bound implies the exact Section 9
paper-scale comparison.  No bound on `q` other than the displayed one is
used. -/
theorem bankPaperCanonical_actualP87Scale_le_secondOrderScale_of_q_upper
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {n : Nat}
    {Cpost Cq tangentConstant : Real}
    (hBn : B.sampleData.n = n)
    (hCpost : 0 <= Cpost)
    (hqUpper : B.q <= Cq * secondOrderScale n)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq <= tangentConstant) :
    Cpost * B.q / B.L <=
      tangentConstant * secondOrderScale n / Real.log (y n) := by
  have hn : 1 < n := by
    simpa only [hBn] using B.n_gt_one
  have hN : 0 <= secondOrderScale n :=
    (secondOrderScale_pos (by omega)).le
  have hqScaled :
      Cpost * B.q <= Cpost * (Cq * secondOrderScale n) :=
    mul_le_mul_of_nonneg_left hqUpper hCpost
  have hqNormalized :
      (2 / 9 : Real) * (Cpost * B.q) <=
        (2 / 9 : Real) * (Cpost * (Cq * secondOrderScale n)) :=
    mul_le_mul_of_nonneg_left hqScaled (by norm_num)
  have hcoefficientScaled :
      ((2 / 9 : Real) * Cpost * Cq) * secondOrderScale n <=
        tangentConstant * secondOrderScale n :=
    mul_le_mul_of_nonneg_right hcoefficient hN
  have hnormalized :
      (2 / 9 : Real) * (Cpost * B.q) <=
        tangentConstant * secondOrderScale n := by
    calc
      (2 / 9 : Real) * (Cpost * B.q) <=
          (2 / 9 : Real) *
            (Cpost * (Cq * secondOrderScale n)) := hqNormalized
      _ = ((2 / 9 : Real) * Cpost * Cq) * secondOrderScale n := by
        ring
      _ <= tangentConstant * secondOrderScale n := hcoefficientScaled
  have hscale :=
    bankPaperCanonical_actualP87Scale_le_paperScale_of_normalized
      B hnormalized
  simpa only [hBn] using hscale

/-! ## The exact downstream package -/



/-! ## Eventual closure -/

/-- Close the seven requested clean-list/budget/scale estimates, together
with the exact logarithmic scale identity, for synchronized actual bridge
data.

The one external asymptotic premise is `hqUpper`.  It is deliberately a
bound only for the actual active mass `B n |>.q`; all clean-list bounds,
the main/error/ceiling budgets, the normalized paper-scale domination, and
the identity `B.L * secondOrderScale n = n` are derived. -/
theorem eventually_bankPaperCanonicalSectionNineBudgetClosure
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : Nat -> BridgeData Head (BankPaperCanonicalExponentBand M))
    (W K0 depth : Nat)
    {c r0 deltaStar rho tangentConstant sigma Cpost Cq : Real}
    (hdelta : 0 < delta)
    (hc : 0 < c)
    (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdeltaStar : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hcleanMainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0)
    (hWtwo : 2 <= W) (hprefix : 2 * depth + 1 <= W)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hwidth :
      delta + M.ratio <=
        bankPaperCanonicalRatioCellPaperWidthChoice
          (tangentPaperCleanListDensity W r0)
          sigma rho tangentConstant)
    (hCpost : 0 <= Cpost)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq <= tangentConstant)
    (hsync :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n ∧
          (B n).sampleData.W = W)
    (hqUpper :
      ∀ᶠ n : Nat in atTop,
        (B n).q <= Cq * secondOrderScale n) :
    ∀ᶠ n : Nat in atTop,
      ∀ (hn : 1 < n) (hW : W ≠ 0)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (S : ScaleSeparation M n W)
        (endpoint : Nat -> Real),
      BankPaperCanonicalSectionNineBudgetClosure
        (K0 := K0) M (B n) R certificate deltaStar sigma
        hdelta hn hW S r0 rho tangentConstant Cpost endpoint := by
  have hr0two : r0 < 2 := hr0three.trans (by norm_num)
  have hdensity :
      0 < tangentPaperCleanListDensity W r0 :=
    tangentPaperCleanListDensity_pos W hr0two
  have hclean :=
    BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed
      W (K0 + 1) hc hr0one hr0three
      hdeltaStar hdeltaUpper hcleanMainSmall
  have herror :=
    eventually_bankPaperCanonical_paperErrorBudget_le
      M W rho tangentConstant
      (tangentPaperCleanListDensity W r0) sigma hdensity hsigma
  have hceiling :=
    eventually_tangentDistributedPaperCeilingBudget_canonical_le
      W hdensity
  have hcutoff :=
    eventually_yNat_lt_centralAnchorCutoff depth
  filter_upwards [hclean, herror, hceiling, hcutoff, hsync, hqUpper] with
    n hcleanN herrorN hceilingN hcutoffN hsyncN hqN
  obtain ⟨hBnN, hBWN⟩ := hsyncN
  intro hn hW R certificate S endpoint
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1)
  let lastCell :=
    bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho
  let residual :=
    bankPaperCanonicalTangentResidual (W := W) R certificate
      fixed candidates endpoint
  let bandOf :=
    bankPaperCanonicalExponentBandOf M hdelta hn hW S
  let cellIndex :=
    bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho
  have hfixedTail :
      fixed ⊆ Finset.Ioc (2 * n)
        (upperEndpoint n (upperTailLength c n)) := by
    simpa only [fixed] using
      R.paperFixedExceptionalFactors_subset_tail deltaStar
  have hgeometry :
      TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
        bandOf cellIndex r0 := by
    dsimp only [bandOf, cellIndex]
    exact bankPaperCanonical_tangentRatioCellGeometry
      (rho := rho) (r0 := r0) M hdelta hn hW S hrho hratio
  have hcleanData :=
    hcleanN depth
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)
      R certificate fixed
      (Band := BankPaperCanonicalExponentBand M)
      lastCell residual bandOf cellIndex (B n).L sigma
      hfixedTail hWtwo hprefix hcutoffN hgeometry
  have hmain :
      tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant (delta + M.ratio) sigma <=
        (tangentPaperCleanListDensity W r0) ^ 2 / 48 :=
    bankPaperCanonical_paperMainBudget_le
      hsigma hrho htangent hwidth
  have htrafficCoefficient :=
    bankPaperCanonical_ratioCellTrafficErrorCoefficient_le_upper
      M hn hWtwo herrorN.1 hrho htangent.le
  have htrafficWeighted :
      16 * bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant <=
        16 * bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
          M W n rho tangentConstant :=
    mul_le_mul_of_nonneg_left htrafficCoefficient (by norm_num)
  have herrorRaw :
      tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellTrafficErrorCoefficient
            M n W rho tangentConstant)
          (bankPaperCanonicalRatioCellIncidentErrorCoefficient
            W n rho tangentConstant)
          sigma <=
        (tangentPaperCleanListDensity W r0) ^ 2 / 96 := by
    apply le_trans ?_ herrorN.2
    unfold tangentDistributedPaperErrorBudget
    exact div_le_div_of_nonneg_right
      (add_le_add htrafficWeighted (le_refl _)) hsigma.le
  have hscaleDom :
      Cpost * (B n).q / (B n).L <=
        tangentConstant * secondOrderScale n / Real.log (y n) :=
    bankPaperCanonical_actualP87Scale_le_secondOrderScale_of_q_upper
      (B n) hBnN hCpost hqN hcoefficient
  have hscale :
      (B n).L * secondOrderScale n = (n : Real) :=
    bankPaperCanonical_bridgeL_mul_secondOrderScale_eq (B n) hBnN
  unfold BankPaperCanonicalSectionNineBudgetClosure
  refine ⟨hBnN, hBWN, ?_, ?_, ?_, hmain, herrorRaw,
    hceilingN, hscaleDom, hscale⟩
  · simpa only [fixed, candidates, lastCell, residual, bandOf, cellIndex,
      BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow] using
      hcleanData.1
  · simpa only [fixed, candidates, lastCell, residual, bandOf, cellIndex,
      BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow] using
      hcleanData.2.1
  · simpa only [fixed, candidates, lastCell, residual, bandOf, cellIndex,
      BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow] using
      hcleanData.2.2

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal008_005.{u_1} := by
  exact @Erdos390.WholePaper.eventually_bankPaperCanonicalSectionNineBudgetClosure
