-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.hasPaperProposition87Conclusion_of_normalizedLawCompanion
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:18:48.270134+00:00
-- url     : https://prove2.me/submissions/625f610a-0431-4829-b779-79e755595cf3

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

/- Source module: Erdos390.Full.FiniteExponentialFamily -/
section


/-!
# Finite exponential families

This file develops the exact finite exponential family used by the smooth-row
bridge.  The sample space is finite, the base weights are nonnegative with
positive total mass, and every score is a continuous linear functional on a
finite-dimensional real parameter space.  All normalization, positivity,
smoothness, and covariance-Jacobian statements are proved from these data.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section



namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]





end FiniteProbability



namespace FiniteExponentialFamily

variable {Ω Param : Type*} [Fintype Ω]
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [FiniteDimensional ℝ Param]





























theorem activeWeight_nonneg (fam : FiniteExponentialFamily Ω Param)
    (ξ : Param) (ω : Ω) : 0 ≤ fam.activeWeight ξ ω :=
  mul_nonneg (le_of_lt fam.baseMass_pos) (fam.probabilityMass_nonneg ξ ω)

theorem activeWeight_sum (fam : FiniteExponentialFamily Ω Param) (ξ : Param) :
    ∑ ω, fam.activeWeight ξ ω = fam.baseMass := by
  simp only [FiniteExponentialFamily.activeWeight]
  rw [← Finset.mul_sum, fam.probabilityMass_sum ξ, mul_one]



























































end FiniteExponentialFamily

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeFitFeasibility -/
section


/-!
# Feasibility and frozen-ledger consequences of the actual bridge tilt

The nonlinear bridge changes only the active structured-cell coordinates.
This file records, for the literal finite exponential family used in
`PaperBridgeFit`, the conclusions which are independent of the analytic
covariance estimates: positivity, preservation of the active mass, an
explicit coordinate ceiling on a preselected parameter ball, and literal
preservation of every frozen top/protected coordinate and integer quota.

The coordinate ceiling is not postulated as a property of the output.  It is
deduced from the exact finite density-ratio estimate and an explicit baseline
slack inequality.  In the final Proposition 8.7 specialization that baseline
slack is discharged by the structured-cell count and the paper's `O(1/L)`
baseline-coordinate bound.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteExponentialFamily

namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]







end StructuredSampleData

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



theorem activeCoordinateWeight_nonneg [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    0 <= B.activeCoordinateWeight xi m :=
  B.vectorFamily.scalarFamily.activeWeight_nonneg xi m



/-- The active smooth-row mass is exactly fixed by every exponential tilt. -/
theorem sum_activeCoordinateWeight [Nonempty Head]
    (xi : B.ParamSpace) :
    (Finset.univ.sum fun m : B.sampleData.Sample =>
      B.activeCoordinateWeight xi m) = B.q := by
  change (Finset.univ.sum fun m : B.sampleData.Sample =>
    B.vectorFamily.scalarFamily.activeWeight xi m) = B.q
  rw [B.vectorFamily.scalarFamily.activeWeight_sum]
  exact B.vectorFamily_baseMass



/-! The paper uses a compact *effective-score* box, not the crude sum of
all score norms.  The next estimates therefore take the correct pointwise
score bound and have constants independent of the number of active cells. -/

theorem exp_neg_effectiveBound_mul_q_le_partition
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R) :
    Real.exp (-R) * B.q <=
      B.vectorFamily.scalarFamily.partition xi := by
  rw [FiniteExponentialFamily.partition]
  calc
    Real.exp (-R) * B.q =
        Finset.univ.sum fun m : B.sampleData.Sample =>
          B.baseline.baseWeight m * Real.exp (-R) := by
      rw [← Finset.sum_mul, B.baseline.baseWeight_sum]
      simp [q, mul_comm]
    _ <= Finset.univ.sum fun m : B.sampleData.Sample =>
        B.vectorFamily.scalarFamily.unnormalizedWeight xi m := by
      apply Finset.sum_le_sum
      intro m _
      simp only [FiniteExponentialFamily.unnormalizedWeight,
        vectorFamily, VectorExponentialFamily.scalarFamily]
      apply mul_le_mul_of_nonneg_left _ (B.baseline.baseWeight_nonneg m)
      apply Real.exp_le_exp.mpr
      exact (neg_le_neg (hscore m)).trans
        (neg_abs_le (B.vectorFamily.scalarFamily.score m xi / B.L))

theorem probabilityMass_le_exp_twoEffectiveBound_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (m : B.sampleData.Sample) :
    B.vectorFamily.probabilityMass xi m <=
      Real.exp (2 * R) * B.vectorFamily.probabilityMass 0 m := by
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  have hZ : 0 < B.vectorFamily.scalarFamily.partition xi :=
    B.vectorFamily.scalarFamily.partition_pos xi
  have hexp : Real.exp (2 * R) * Real.exp (-R) = Real.exp R := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [B.probabilityMass_zero m]
  change B.vectorFamily.scalarFamily.unnormalizedWeight xi m /
      B.vectorFamily.scalarFamily.partition xi <=
    Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)
  apply (div_le_iff₀ hZ).2
  calc
    B.vectorFamily.scalarFamily.unnormalizedWeight xi m =
        B.baseline.baseWeight m *
          Real.exp (B.vectorFamily.scalarFamily.score m xi / B.L) := by
      rfl
    _ <= B.baseline.baseWeight m * Real.exp R := by
      apply mul_le_mul_of_nonneg_left _ (B.baseline.baseWeight_nonneg m)
      exact Real.exp_le_exp.mpr
        ((le_abs_self _).trans (hscore m))
    _ = (Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)) *
        (Real.exp (-R) * B.q) := by
      field_simp [hq]
      calc
        B.baseline.baseWeight m * Real.exp R =
            B.baseline.baseWeight m *
              (Real.exp (2 * R) * Real.exp (-R)) := by rw [hexp]
        _ = B.baseline.baseWeight m * Real.exp (2 * R) *
              Real.exp (-R) := by ring
    _ <= (Real.exp (2 * R) * (B.baseline.baseWeight m / B.q)) *
        B.vectorFamily.scalarFamily.partition xi := by
      exact mul_le_mul_of_nonneg_left
        (B.exp_neg_effectiveBound_mul_q_le_partition xi R hscore)
        (mul_nonneg (le_of_lt (Real.exp_pos _))
          (div_nonneg (B.baseline.baseWeight_nonneg m)
            (le_of_lt B.q_pos)))

theorem activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
    [Nonempty Head] (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (m : B.sampleData.Sample) :
    B.activeCoordinateWeight xi m <=
      Real.exp (2 * R) * B.baseline.baseWeight m := by
  rw [activeCoordinateWeight, FiniteExponentialFamily.activeWeight]
  change B.vectorFamily.baseMass * B.vectorFamily.probabilityMass xi m <=
    Real.exp (2 * R) * B.baseline.baseWeight m
  rw [B.vectorFamily_baseMass]
  calc
    B.q * B.vectorFamily.probabilityMass xi m <=
        B.q * (Real.exp (2 * R) *
          B.vectorFamily.probabilityMass 0 m) :=
      mul_le_mul_of_nonneg_left
        (B.probabilityMass_le_exp_twoEffectiveBound_mul_baseline
          xi R hscore m) (le_of_lt B.q_pos)
    _ = Real.exp (2 * R) * B.baseline.baseWeight m := by
      rw [B.probabilityMass_zero m]
      field_simp [ne_of_gt B.q_pos]







/-! ## Actual natural-number coordinates -/



theorem ambientActiveWeight_nonneg [Nonempty Head]
    (xi : B.ParamSpace) (a : Nat) :
    0 <= B.ambientActiveWeight xi a := by
  apply Finset.sum_nonneg
  intro m _
  split_ifs
  · exact B.activeCoordinateWeight_nonneg xi m
  · exact le_rfl

theorem ambientActiveWeight_eq_of_value
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.ambientActiveWeight xi (B.sampleData.value m) =
      B.activeCoordinateWeight xi m := by
  classical
  rw [ambientActiveWeight, Finset.sum_eq_single m]
  · simp
  · intro k _ hkm
    rw [if_neg]
    intro hvalue
    exact hkm
      (B.sampleData.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

theorem ambientActiveWeight_eq_zero_of_not_value
    [Nonempty Head] (xi : B.ParamSpace) (a : Nat)
    (ha : forall m : B.sampleData.Sample, B.sampleData.value m ≠ a) :
    B.ambientActiveWeight xi a = 0 := by
  rw [ambientActiveWeight]
  apply Finset.sum_eq_zero
  intro m _
  rw [if_neg (ha m)]





/-- Feasibility in the paper's correct compact effective-score box.  Unlike
the preceding crude Euclidean-ball corollary, this bound has no factor equal
to the number of active coordinates and is the form consumed by the final
non-circular ODE argument. -/
theorem ambientCombinedWeight_mem_Icc_of_effectiveScoreBound
    [Nonempty Head]
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : Nat -> Real)
    (hfrozen : forall a, frozenWeight a ∈ Set.Icc (0 : Real) 1)
    (xi : B.ParamSpace) (R : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= R)
    (hslack : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <= 1) :
    forall a : Nat,
      B.ambientCombinedWeight frozenWeight xi a ∈ Set.Icc (0 : Real) 1 := by
  intro a
  constructor
  · exact add_nonneg (hfrozen a).1 (B.ambientActiveWeight_nonneg xi a)
  · by_cases ha : exists m : B.sampleData.Sample, B.sampleData.value m = a
    · obtain ⟨m, hm⟩ := ha
      rw [ambientCombinedWeight, ← hm,
        B.ambientActiveWeight_eq_of_value hsep xi m]
      calc
        frozenWeight (B.sampleData.value m) + B.activeCoordinateWeight xi m
            <= frozenWeight (B.sampleData.value m) +
              Real.exp (2 * R) * B.baseline.baseWeight m := by
          simpa [add_comm] using add_le_add_left
            (B.activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
              xi R hscore m)
            (frozenWeight (B.sampleData.value m))
        _ <= 1 := hslack m
    · rw [ambientCombinedWeight,
        B.ambientActiveWeight_eq_zero_of_not_value xi a
          (fun m hm => ha ⟨m, hm⟩), add_zero]
      exact (hfrozen a).2



/-! ## Frozen top/protected coordinates and the integer ledger -/









/-- Frozen coordinates are literally unchanged between any two bridge
parameters, not merely equal in total mass. -/
theorem combinedWeight_fixed_unchanged [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi eta : B.ParamSpace) (f : Fixed) :
    B.combinedWeight fixedWeight xi (Sum.inl f) =
      B.combinedWeight fixedWeight eta (Sum.inl f) := rfl

theorem sum_combinedWeight [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (fixedWeight : Fixed -> Real) (xi : B.ParamSpace) :
    (Finset.univ.sum fun a : Fixed ⊕ B.sampleData.Sample =>
      B.combinedWeight fixedWeight xi a) =
      (Finset.univ.sum fixedWeight) + B.q := by
  rw [Fintype.sum_sum_type]
  simp only [combinedWeight]
  rw [B.sum_activeCoordinateWeight xi]

/-- The exact integer smooth-row quota is preserved because the active mass
is fixed and every other ledger entry is frozen. -/
theorem sum_combinedWeight_eq_integerQuota [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (fixedWeight : Fixed -> Real) (quota : Int)
    (hquota : (quota : Real) =
      (Finset.univ.sum fixedWeight) + B.q)
    (xi : B.ParamSpace) :
    (Finset.univ.sum fun a : Fixed ⊕ B.sampleData.Sample =>
      B.combinedWeight fixedWeight xi a) = (quota : Real) := by
  rw [B.sum_combinedWeight fixedWeight xi, ← hquota]



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperBaselineSlack -/
section


/-!
# Converting the baseline `O(1 / log n)` ledger into coordinate slack

The baseline active-measure lemma and the protected-floor construction give
separate `C / L` bounds.  This file contains the exact finite inequality which
turns those bounds into the combined ceiling required after a compact
effective tilt.  Thus Proposition 8.7 need not assume its final `[0,1]`
conclusion.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- Separate `C/L` bounds imply the exact frozen-plus-active baseline slack
once `L` exceeds the displayed fixed constant. -/
theorem combinedBaselineSlack_of_div_log_bounds
    [Nonempty Head]
    (frozenWeight : Nat -> Real) (Cfixed Cactive R : Real)
    (hfrozen : forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) <= Cfixed / B.L)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Cfixed + Real.exp (2 * R) * Cactive <= B.L) :
    forall m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <= 1 := by
  intro m
  calc
    frozenWeight (B.sampleData.value m) +
        Real.exp (2 * R) * B.baseline.baseWeight m <=
      Cfixed / B.L + Real.exp (2 * R) * (Cactive / B.L) :=
        add_le_add (hfrozen m) (mul_le_mul_of_nonneg_left
          (hactive m) (le_of_lt (Real.exp_pos _)))
    _ = (Cfixed + Real.exp (2 * R) * Cactive) / B.L := by ring
    _ <= B.L / B.L :=
      div_le_div_of_nonneg_right hlarge (le_of_lt B.L_pos)
    _ = 1 := div_self (ne_of_gt B.L_pos)



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperEffectiveScoreBound -/
section


/-!
# Dimension-free score control in the paper's effective parameter norm

The Euclidean parameter norm has one coordinate per prime band and is not the
norm used in the non-circular argument of Proposition 8.7.  This file proves
the exact re-expansion of the finite exponential-family score into the
effective prime fugacities and the fixed nuisance block.  It then obtains a
pointwise score bound whose constant is independent of the number of bands.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit
namespace BridgeData

open ArithmeticModel ArithmeticBandGeometry
open Erdos390.Full.PaperStatisticNorm
open Erdos390.Full.PaperStatisticNorm.BridgeData

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)













/-! ## Dimension-free pointwise bounds -/















/-- Literal natural-coordinate feasibility from the paper effective box and
the two proved `O(1/L)` ledgers.  Unlike the earlier Euclidean corollary, its
constant does not grow with the number of prime bands. -/
theorem ambientCombinedWeight_mem_Icc_of_paperEffectiveSize
    [Nonempty Head]
    {C a Cfixed Cactive : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : ℕ → ℝ)
    (hfrozenFeasible : ∀ x, frozenWeight x ∈ Set.Icc (0 : ℝ) 1)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a)
    (hfrozen : ∀ m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactive : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * a)) * Cactive ≤ B.L) :
    ∀ x : ℕ,
      B.ambientCombinedWeight frozenWeight xi x ∈ Set.Icc (0 : ℝ) 1 := by
  let R := (valuationLogCoefficient C B.sampleData.W +
    B.nuisanceStatisticCoefficient C) * a
  apply B.ambientCombinedWeight_mem_Icc_of_effectiveScoreBound
    hsep frozenWeight hfrozenFeasible xi R
      (B.effectiveScoreBound_of_paperEffectiveSize hC hW hhi xi hxi)
  exact B.combinedBaselineSlack_of_div_log_bounds frozenWeight
    Cfixed Cactive R hfrozen hactive (by simpa only [R] using hlarge)

end

end BridgeData
end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalActiveMassBaseline -/
section


/-!
# Literal-active-mass variant of the canonical barycentric baseline

`BarycentricTarget.baseline` is the normalized probability allocation used
throughout the existing covariance chain.  The paper's actual bridge uses
the same normalized cell law with total mass `q_n`, generally of order
`n / log n`.  This backward-compatible module supplies that scaled
allocation without changing `BarycentricTarget` or any existing theorem
signature.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit

noncomputable section

namespace PaperGuardCensus.BarycentricTarget

variable {Head : Type*} [Fintype Head] [Nonempty Head]
  {D : StructuredSampleData Head} (T : BarycentricTarget D)





omit [Nonempty Head] in
/-- Scaling leaves the normalized law on the structured cells unchanged. -/
theorem activeMassBaseline_normalizedCellMass
    (q : Real) (hq : 0 < q) (c : Cell Head) :
    (T.activeMassBaseline q hq).normalizedCellMass c =
      T.cellProbability c := by
  unfold BaselineAllocation.normalizedCellMass
  change (q * T.cellProbability c) /
      (T.activeMassBaseline q hq).totalMass = T.cellProbability c
  rw [T.activeMassBaseline_totalMass q hq]
  field_simp [ne_of_gt hq]







end PaperGuardCensus.BarycentricTarget

namespace PaperBridgeFit.BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band] [Nonempty Head]
  (B : BridgeData Head Band)







end PaperBridgeFit.BridgeData

end


end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperProposition87ActiveMassTransport -/
section


/-!
# Homogeneous active-mass transport for Proposition 8.7

The canonical covariance argument is an argument about the normalized cell
law.  The literal bridge, however, has total active mass `q_n`, not one.
This file makes the homogeneity exact without changing any of the existing
Proposition 8.7 interfaces.

For a bridge whose baseline is `T.activeMassBaseline q hq`, we form the
mass-one companion with the same sample, partition, gauge, reference head,
and scale, and with baseline `T.baseline`.  We prove that

* the two tilted probability laws and normalized covariances agree;
* every active weight and raw paper moment for the literal bridge is `q`
  times its companion value;
* after dividing the requested raw moment increment by `q`, the two ODE
  vector fields agree exactly, including at points where the globally
  defined inverse is the zero fallback; and
* a companion Proposition 8.7 path therefore transports to a literal
  `q`-mass path.  Feasibility is proved afresh with the literal frozen and
  active ledgers, so protected frozen mass may overlap an active coordinate.

No equality between the literal baseline and the old mass-one baseline is
assumed.
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



















/-- Literal coordinate weights are exactly `q` times the mass-one companion
weights. -/
theorem baseWeight_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (m : B.sampleData.Sample) :
    B.baseline.baseWeight m =
      q * (B.normalizedLawCompanion T).baseline.baseWeight m := by
  rw [hbaseline, T.activeMassBaseline_baseWeight q hq]
  rfl

/-- The centered head statistics agree because scaling does not change the
normalized cell law. -/
theorem headBaselineMass_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq) (h : Head) :
    B.headBaselineMass h =
      (B.normalizedLawCompanion T).headBaselineMass h := by
  unfold headBaselineMass normalizedLawCompanion
  rw [hbaseline]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [T.activeMassBaseline_normalizedCellMass q hq,
    T.baseline_normalizedCellMass]

/-- The full statistic vector is unchanged by active-mass scaling. -/
theorem statistic_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (m : B.sampleData.Sample) :
    B.statistic m = (B.normalizedLawCompanion T).statistic m := by
  apply (EuclideanSpace.equiv B.Coord Real).injective
  funext c
  change B.statistic m c = (B.normalizedLawCompanion T).statistic m c
  rw [B.statistic_apply,
    (B.normalizedLawCompanion T).statistic_apply]
  cases c with
  | gauge j => rfl
  | physical => rfl
  | head h =>
      change
        (B.headIndicator h.1 m - B.headBaselineMass h.1) / 1 =
          (B.headIndicator h.1 m -
            (B.normalizedLawCompanion T).headBaselineMass h.1) / 1
      rw [B.headBaselineMass_eq_normalizedLawCompanion
        T q hq hbaseline h.1]
  | slow => rfl

/-- Unnormalized tilted weights scale by `q`. -/
theorem unnormalizedWeight_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.unnormalizedWeight xi m =
      q * (B.normalizedLawCompanion T).vectorFamily.scalarFamily.unnormalizedWeight
        xi m := by
  have hbase :
      B.vectorFamily.scalarFamily.baseWeight m =
        q * (B.normalizedLawCompanion T).vectorFamily.scalarFamily.baseWeight m := by
    change B.baseline.baseWeight m =
      q * (B.normalizedLawCompanion T).baseline.baseWeight m
    exact B.baseWeight_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline m
  have hscore :
      B.vectorFamily.scalarFamily.score m xi =
        (B.normalizedLawCompanion T).vectorFamily.scalarFamily.score m xi := by
    change (innerSL ℝ) (B.statistic m) xi =
      (innerSL ℝ) ((B.normalizedLawCompanion T).statistic m) xi
    rw [B.statistic_eq_normalizedLawCompanion T q hq hbaseline m]
    rfl
  have hscale :
      B.vectorFamily.scalarFamily.scale =
        (B.normalizedLawCompanion T).vectorFamily.scalarFamily.scale := by
    change B.L = (B.normalizedLawCompanion T).L
    exact (B.normalizedLawCompanion_L T).symm
  unfold FiniteExponentialFamily.unnormalizedWeight
  rw [hbase, hscore, hscale]
  ring

/-- Partition functions scale by `q`. -/
theorem partition_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    B.vectorFamily.scalarFamily.partition xi =
      q * (B.normalizedLawCompanion T).vectorFamily.scalarFamily.partition xi := by
  unfold FiniteExponentialFamily.partition
  simp_rw [B.unnormalizedWeight_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline xi]
  rw [Finset.mul_sum]
  rfl

/-- The tilted probability mass is independent of the literal active mass. -/
theorem probabilityMass_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.probabilityMass xi m =
      (B.normalizedLawCompanion T).vectorFamily.scalarFamily.probabilityMass
        xi m := by
  have hpartition :
      (B.normalizedLawCompanion T).vectorFamily.scalarFamily.partition xi ≠ 0 :=
    (B.normalizedLawCompanion T).vectorFamily.scalarFamily.partition_ne_zero xi
  unfold FiniteExponentialFamily.probabilityMass
  rw [B.unnormalizedWeight_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline xi m,
    B.partition_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline xi]
  field_simp [ne_of_gt hq, hpartition]



/-- Active tilted coordinate weights scale by `q`. -/
theorem activeWeight_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.activeWeight xi m =
      q * (B.normalizedLawCompanion T).vectorFamily.scalarFamily.activeWeight
        xi m := by
  unfold FiniteExponentialFamily.activeWeight
  change
    B.vectorFamily.baseMass *
        B.vectorFamily.scalarFamily.probabilityMass xi m =
      q * ((B.normalizedLawCompanion T).vectorFamily.baseMass *
        (B.normalizedLawCompanion T).vectorFamily.scalarFamily.probabilityMass
          xi m)
  rw [B.vectorFamily_baseMass,
    B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline,
    (B.normalizedLawCompanion T).vectorFamily_baseMass,
    B.normalizedLawCompanion_q T,
    B.probabilityMass_eq_normalizedLawCompanion T q hq hbaseline xi m]
  ring

/-- Every raw paper moment scales by the literal active mass. -/
theorem paperMoment_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (F : B.sampleData.Sample -> Real) (xi : B.ParamSpace) :
    B.paperMoment F xi =
      q * (B.normalizedLawCompanion T).paperMoment F xi := by
  unfold paperMoment FiniteExponentialFamily.moment
  simp_rw [B.activeWeight_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline xi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The vector moment map scales by `q`. -/
theorem vectorMoment_eq_activeMass_smul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    B.vectorFamily.vectorMoment xi =
      q • (B.normalizedLawCompanion T).vectorFamily.vectorMoment xi := by
  unfold VectorExponentialFamily.vectorMoment
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [B.activeWeight_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline xi m]
  have hstatistic :
      B.vectorFamily.statistic m =
        (B.normalizedLawCompanion T).vectorFamily.statistic m := by
    change B.statistic m = (B.normalizedLawCompanion T).statistic m
    exact B.statistic_eq_normalizedLawCompanion T q hq hbaseline m
  rw [hstatistic]
  rw [mul_smul]

set_option backward.isDefEq.respectTransparency true in
/-- Consequently the raw Jacobian scales by `q`. -/
theorem jacobian_eq_activeMass_smul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    B.vectorFamily.jacobian xi =
      q • (B.normalizedLawCompanion T).vectorFamily.jacobian xi := by
  have hbase :=
    (B.normalizedLawCompanion T).vectorFamily.hasFDerivAt_vectorMoment xi
  have hscaled := hbase.const_smul q
  have hfun :
      (fun eta : B.ParamSpace =>
        q • (B.normalizedLawCompanion T).vectorFamily.vectorMoment eta) =
        B.vectorFamily.vectorMoment := by
    funext eta
    exact (B.vectorMoment_eq_activeMass_smul_normalizedLawCompanion
      T q hq hbaseline eta).symm
  exact B.vectorFamily.hasFDerivAt_vectorMoment xi |>.unique (hfun ▸ hscaled)

/-- Applying the raw Jacobian exhibits the same scale factor. -/
theorem jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi v : B.ParamSpace) :
    B.vectorFamily.jacobian xi v =
      q • (B.normalizedLawCompanion T).vectorFamily.jacobian xi v := by
  rw [B.jacobian_eq_activeMass_smul_normalizedLawCompanion
    T q hq hbaseline xi]
  rfl



/-- Dividing the raw band request by `q` makes the target vectors differ by
the same factor `q` as the Jacobians. -/
theorem targetVector_eq_activeMass_smul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (Delta : Band -> Real) :
    B.targetVector Delta = q •
      (B.normalizedLawCompanion T).targetVector
        (fun j => Delta j / q) := by
  apply (EuclideanSpace.equiv B.Coord Real).injective
  funext c
  change B.targetVector Delta c = q *
    (B.normalizedLawCompanion T).targetVector
      (fun j => Delta j / q) c
  rw [B.targetVector_apply,
    (B.normalizedLawCompanion T).targetVector_apply]
  cases c with
  | gauge j =>
      change
        (Delta j.1 - B.lowRatio j * Delta B.lowBand) / 1 =
          q * ((Delta j.1 / q -
            B.lowRatio j * (Delta B.lowBand / q)) / 1)
      field_simp [ne_of_gt hq]
  | physical => simp [unscaledTarget, coordScale]
  | head h => simp [unscaledTarget, coordScale]
  | slow =>
      change
        (∑ j : Band, B.bandCenter j * Delta j) / B.w =
          q * ((∑ j : Band, B.bandCenter j * (Delta j / q)) / B.w)
      have hsum :
          (∑ j : Band, B.bandCenter j * (Delta j / q)) =
            (∑ j : Band, B.bandCenter j * Delta j) / q := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hsum]
      field_simp [ne_of_gt hq, ne_of_gt B.w_pos]











/-- Raw Jacobian invertibility is invariant under positive active-mass
scaling.  This is used to handle the globally defined inverse even outside
the covariance box, where its documented fallback is zero. -/
theorem jacobian_isInvertible_iff_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (xi : B.ParamSpace) :
    (B.vectorFamily.jacobian xi).IsInvertible <->
      ((B.normalizedLawCompanion T).vectorFamily.jacobian xi).IsInvertible := by
  constructor
  · intro hB
    have hinj : Function.Injective
        ((B.normalizedLawCompanion T).vectorFamily.jacobian xi) := by
      intro x y hxy
      apply hB.injective
      rw [B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
          T q hq hbaseline xi,
        B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
          T q hq hbaseline xi,
        hxy]
    have hsurj : Function.Surjective
        ((B.normalizedLawCompanion T).vectorFamily.jacobian xi) :=
      LinearMap.surjective_of_injective hinj
    exact ⟨ContinuousLinearEquiv.ofBijective
      ((B.normalizedLawCompanion T).vectorFamily.jacobian xi)
      (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj), rfl⟩
  · intro hN
    have hinj : Function.Injective (B.vectorFamily.jacobian xi) := by
      intro x y hxy
      apply hN.injective
      have hscaled := hxy
      rw [B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
          T q hq hbaseline xi,
        B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
          T q hq hbaseline xi] at hscaled
      exact smul_right_injective B.ParamSpace (ne_of_gt hq) hscaled
    have hsurj : Function.Surjective (B.vectorFamily.jacobian xi) :=
      LinearMap.surjective_of_injective hinj
    exact ⟨ContinuousLinearEquiv.ofBijective
      (B.vectorFamily.jacobian xi)
      (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj), rfl⟩

/-- The straight-target ODE is exactly homogeneous: scaling the baseline
and the raw requested increments by the same positive factor does not alter
the parameter-space vector field. -/
theorem vectorField_eq_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (Delta : Band -> Real) (xi : B.ParamSpace) :
    B.vectorFamily.vectorField (B.targetVector Delta) xi =
      (B.normalizedLawCompanion T).vectorFamily.vectorField
        ((B.normalizedLawCompanion T).targetVector
          (fun j => Delta j / q)) xi := by
  let N : BridgeData Head Band := B.normalizedLawCompanion T
  by_cases hN : (N.vectorFamily.jacobian xi).IsInvertible
  · have hB : (B.vectorFamily.jacobian xi).IsInvertible :=
      (B.jacobian_isInvertible_iff_normalizedLawCompanion
        T q hq hbaseline xi).mpr hN
    apply hB.injective
    change B.vectorFamily.jacobian xi
        ((B.vectorFamily.jacobian xi).inverse (B.targetVector Delta)) =
      B.vectorFamily.jacobian xi
        ((N.vectorFamily.jacobian xi).inverse
          (N.targetVector (fun j => Delta j / q)))
    rw [hB.self_apply_inverse]
    rw [B.jacobian_apply_eq_activeMass_smul_normalizedLawCompanion
      T q hq hbaseline xi]
    rw [hN.self_apply_inverse]
    exact B.targetVector_eq_activeMass_smul_normalizedLawCompanion
      T q hq Delta
  · have hB : ¬ (B.vectorFamily.jacobian xi).IsInvertible := by
      intro h
      exact hN ((B.jacobian_isInvertible_iff_normalizedLawCompanion
        T q hq hbaseline xi).mp h)
    unfold VectorExponentialFamily.vectorField
    rw [ContinuousLinearMap.inverse_of_not_isInvertible hB,
      ContinuousLinearMap.inverse_of_not_isInvertible hN]
    change (0 : B.ParamSpace) = (0 : B.ParamSpace)
    rfl

/-- The marked residual itself scales by `q` when both the baseline and the
marked target are scaled. -/
theorem markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (markedTarget : Nat -> Real) (xi : B.ParamSpace) (j : Band) :
    B.markedBandResidual markedTarget xi j = q *
      (B.normalizedLawCompanion T).markedBandResidual
        (fun p => markedTarget p / q) xi j := by
  unfold markedBandResidual
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hvaluation :
      B.markedValuation (p : Nat) =
        (B.normalizedLawCompanion T).markedValuation (p : Nat) := by
    rfl
  rw [hvaluation]
  rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline]
  field_simp [ne_of_gt hq]

set_option maxHeartbeats 4000000 in
/--
Transport a certified mass-one canonical Proposition 8.7 path to the
literal active mass.  The auxiliary frozen layer used to obtain the
mass-one path is deliberately independent of the literal frozen layer and
is discarded.  Literal feasibility, frozen invariance, mass, and quota are
then re-established directly from the ordinary Proposition 8.7 ledger
hypotheses.  This avoids any false requirement that `q - 1` be an integer
or that the protected layer be disjoint from the active support.
-/
theorem hasPaperProposition87Conclusion_of_normalizedLawCompanion
    [Nonempty Head]
    {Aux Fixed : Type*} [Fintype Aux] [Fintype Fixed]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (Delta : Band -> Real) (a : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (auxValue : Aux -> Nat) (auxWeight : Aux -> Real) (auxQuota : Int)
    (Hnormalized : (B.normalizedLawCompanion T).HasPaperProposition87Conclusion
        (fun j => Delta j / q) a (fun p => markedTarget p / q)
        (N / q) Cpost auxValue auxWeight auxQuota)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int)
    (hquota : (quota : Real) = (∑ f, fixedWeight f) + B.q)
    {C Cfixed Cactive : Real}
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sigma, B.sampleData.hi sigma <=
      ArithmeticModel.physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hfrozenFeasible : forall x,
      frozenAmbientWeight fixedValue fixedWeight x ∈ Icc (0 : Real) 1)
    (hfrozenLedger : forall m : B.sampleData.Sample,
      frozenAmbientWeight fixedValue fixedWeight (B.sampleData.value m) <=
        Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * (3 * (a : Real)))) *
            Cactive <= B.L) :
    B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
      fixedValue fixedWeight quota := by
  let B0 : BridgeData Head Band := B.normalizedLawCompanion T
  obtain ⟨path, hpath0, hbands0⟩ := Hnormalized
  rcases hpath0 with
    ⟨hzero0, hball0, _hsize0, hderiv0, hbandMoments0, hphysical0,
      hordinaryLog0, hheads0, hsmall0, hprimeLog0, hmarked0,
      _hfeasible0, _hfixed0, _hmass0, _hquota0⟩
  have hzero : path 0 = 0 := hzero0
  have hball : ∀ t ∈ Icc (0 : Real) 1,
      B.effectiveParamEquiv.symm (path t) ∈
        closedBall (0 : B.EffectiveParamSpace) (a : Real) := by
    intro t ht
    have ht0 := hball0 t ht
    rw [mem_closedBall, dist_zero_right,
      B0.norm_effectiveParamEquiv_symm] at ht0
    rw [mem_closedBall, dist_zero_right,
      B.norm_effectiveParamEquiv_symm]
    have hnorm :
        ‖B.effectiveCoordinateCLM (path t)‖ =
          ‖B0.effectiveCoordinateCLM (path t)‖ := by
      rw [B.norm_effectiveCoordinateCLM_eq,
        B0.norm_effectiveCoordinateCLM_eq]
      unfold effectivePrimeCoefficient bandParameter nuisanceParameter
        HeadIndex lowRatio harmonicMass primeDeviation bandCenter
      simp only [B0, B.normalizedLawCompanion_sampleData T,
        B.normalizedLawCompanion_partition T,
        B.normalizedLawCompanion_lowBand T,
        B.normalizedLawCompanion_referenceHead T,
        B.normalizedLawCompanion_w T]
      congr 1
      congr 1
      congr 1
      apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) Real).injective
      funext c
      cases c <;> rfl
    rw [hnorm]
    exact ht0
  have hsize : ∀ t ∈ Icc (0 : Real) 1,
      B.paperEffectiveSize (path t) <= 3 * (a : Real) := by
    intro t ht
    let z : B.EffectiveParamSpace := B.effectiveParamEquiv.symm (path t)
    have hzBall : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : Real) :=
      hball t ht
    have hzNorm : ‖z‖ <= (a : Real) := by
      simpa only [mem_closedBall, dist_zero_right] using hzBall
    have hpath : B.effectiveParamEquiv z = path t :=
      B.effectiveParamEquiv.apply_symm_apply (path t)
    rw [← hpath]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hzNorm (by norm_num))
  set_option backward.isDefEq.respectTransparency true in
  have hderiv : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path
        (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
        (Icc (0 : Real) 1) t := by
    intro t ht
    rw [B.vectorField_eq_normalizedLawCompanion
      T q hq hbaseline Delta (path t)]
    exact hderiv0 t ht
  have hbandMoments : forall j : Band,
      B.paperMoment (B.bandScore j) (path 1) =
        B.paperMoment (B.bandScore j) 0 + Delta j := by
    intro j
    have hj := hbandMoments0 j
    have hj' :
        B0.paperMoment (B.bandScore j) (path 1) =
          B0.paperMoment (B.bandScore j) 0 + Delta j / q := by
      simpa only [B0, normalizedLawCompanion] using hj
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    rw [hj']
    field_simp [ne_of_gt hq]; ring <;> rfl
  have hphysical : B.paperMoment B.physicalScore (path 1) =
      B.paperMoment B.physicalScore 0 := by
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hphysical0)
  have hordinaryLog : B.paperMoment B.ordinaryLogScore (path 1) =
      B.paperMoment B.ordinaryLogScore 0 := by
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hordinaryLog0)
  have hheads : forall h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) (path 1) =
        B.paperMoment (B.headIndicator h.1) 0 := by
    intro h
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hheads0 h)
  have hsmall : forall p : Nat, p.Prime -> p <= B.sampleData.W ->
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0 := by
    intro p hp hple
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hsmall0 p hp hple)
  have hprimeLog : B.paperMoment B.primeLogScore (path 1) =
      B.paperMoment B.primeLogScore 0 := by
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline,
      B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
        T q hq hbaseline]
    exact congrArg (fun x : Real => q * x) (by
      simpa only [B0, normalizedLawCompanion] using hprimeLog0)
  have hmarked : ∀ p ∈ ArithmeticModel.primeBand
      B.sampleData.n B.sampleData.W,
      abs (markedTarget p -
          B.paperMoment (B.markedValuation p) (path 1)) <=
        Cpost * N / ((p : Real) * B.L) := by
    intro p hp
    have hp0 := hmarked0 p (by
      simpa only [B0, normalizedLawCompanion] using hp)
    rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
      T q hq hbaseline]
    have hidentity : markedTarget p - q *
          B0.paperMoment (B.markedValuation p) (path 1) =
        q * (markedTarget p / q -
          B0.paperMoment (B.markedValuation p) (path 1)) := by
      field_simp [ne_of_gt hq]
    rw [hidentity, abs_mul, abs_of_pos hq]
    have hscaled := mul_le_mul_of_nonneg_left hp0 hq.le
    have hcancel : q * (N / q) = N := by
      field_simp [ne_of_gt hq]
    calc
      q * abs (markedTarget p / q -
          B0.paperMoment (B.markedValuation p) (path 1))
          <= q * (Cpost * (N / q) / ((p : Real) * B.L)) := hscaled
      _ = (q * (N / q)) *
          (Cpost / ((p : Real) * B.L)) := by ring
      _ = N * (Cpost / ((p : Real) * B.L)) := by rw [hcancel]
      _ = Cpost * N / ((p : Real) * B.L) := by ring
  have hfeasible : ∀ t ∈ Icc (0 : Real) 1, forall x : Nat,
      B.ambientCombinedWeight
          (frozenAmbientWeight fixedValue fixedWeight) (path t) x ∈
        Icc (0 : Real) 1 := by
    intro t ht
    exact B.ambientCombinedWeight_mem_Icc_of_paperEffectiveSize
      hC hW hhi hsep
      (frozenAmbientWeight fixedValue fixedWeight) hfrozenFeasible
      (path t) (hsize t ht) hfrozenLedger hactiveLedger hlarge
  have hfixed : ∀ t ∈ Icc (0 : Real) 1, forall f : Fixed,
      B.combinedWeight fixedWeight (path t) (Sum.inl f) =
        B.combinedWeight fixedWeight 0 (Sum.inl f) := by
    intro t ht f
    exact B.combinedWeight_fixed_unchanged fixedWeight (path t) 0 f
  have hmass : ∀ t ∈ Icc (0 : Real) 1,
      (∑ m : B.sampleData.Sample,
        B.activeCoordinateWeight (path t) m) = B.q := by
    intro t ht
    exact B.sum_activeCoordinateWeight (path t)
  have hquotaPath : ∀ t ∈ Icc (0 : Real) 1,
      (∑ x : Fixed ⊕ B.sampleData.Sample,
        B.combinedWeight fixedWeight (path t) x) = (quota : Real) := by
    intro t ht
    exact B.sum_combinedWeight_eq_integerQuota
      fixedWeight quota hquota (path t)
  have hpath : B.IsPaperProposition87Path Delta a markedTarget N Cpost
      fixedValue fixedWeight quota path :=
    ⟨hzero, hball, hsize, hderiv, hbandMoments, hphysical,
      hordinaryLog, hheads, hsmall, hprimeLog, hmarked, hfeasible,
      hfixed, hmass, hquotaPath⟩
  refine ⟨path, hpath, ?_⟩
  intro j
  rw [B.markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline markedTarget (path 1) j]
  have hj := hbands0 j
  change q * B0.markedBandResidual
      (fun p => markedTarget p / q) (path 1) j = 0
  rw [hj, mul_zero]



end BridgeData

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs



namespace BridgeData



end BridgeData

/-!
## Varying paper mass

The paper uses `q_n`, not a fixed `q`.  Uniformity is retained once
`1 <= q_n`: the normalized companion ledger is bounded by
`(Cactive / q_n) / L <= Cactive / L`, so no ODE radius, mesh constant, or
eventual threshold needs to depend on `q_n`.
-/



namespace BridgeData



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2 u_3 u_4
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head] {Aux : Type u_3}
  {Fixed : Type u_4} [inst_5 : Fintype.{u_3} Aux] [inst_6 : Fintype.{u_4} Fixed]
  (T :
    Erdos390.Full.PaperGuardCensus.BarycentricTarget.{u_1}
      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
  (q : Real) (hq : LT.lt.{0} (0 : Real) q),
  Eq.{u_1 + 1} (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B)
      (Erdos390.Full.PaperGuardCensus.BarycentricTarget.activeMassBaseline.{u_1} T q hq) →
    ∀ (Delta : Band → Real) (a : NNReal) (markedTarget : Nat → Real) (N Cpost : Real) (auxValue : Aux → Nat)
      (auxWeight : Aux → Real) (auxQuota : Int),
      Erdos390.Full.PaperBridgeFit.BridgeData.HasPaperProposition87Conclusion.{u_1, u_2, u_3}
          (Erdos390.Full.PaperBridgeFit.BridgeData.normalizedLawCompanion.{u_1, u_2} B T)
          (fun j => HDiv.hDiv.{0, 0, 0} (Delta j) q) a (fun p => HDiv.hDiv.{0, 0, 0} (markedTarget p) q)
          (HDiv.hDiv.{0, 0, 0} N q) Cpost auxValue auxWeight auxQuota →
        ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real) (quota : Int),
          Eq.{1} (↑quota)
              (HAdd.hAdd.{0, 0, 0} (∑ f, fixedWeight f) (Erdos390.Full.PaperBridgeFit.BridgeData.q.{u_1, u_2} B)) →
            ∀ {C Cfixed Cactive : Real},
              LE.le.{0} (1 : Real) C →
                LT.lt.{0} (1 : Nat)
                    (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)) →
                  (∀ (sigma : Erdos390.Full.PaperBridgeFit.PhysicalSign),
                      LE.le.{0}
                        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.hi.{u_1}
                          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) sigma)
                        (Erdos390.Full.ArithmeticModel.physicalBound C
                          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))) →
                    Erdos390.Full.PaperBridgeFit.StructuredSampleData.HeadPatternsSeparated.{u_1}
                        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) →
                      (∀ (x : Nat),
                          Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) (1 : Real))
                            (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_4} fixedValue fixedWeight
                              x)) →
                        (∀
                            (m :
                              Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                            LE.le.{0}
                              (Erdos390.Full.PaperBridgeFit.BridgeData.frozenAmbientWeight.{u_4} fixedValue fixedWeight
                                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.value.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B) m))
                              (HDiv.hDiv.{0, 0, 0} Cfixed (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B))) →
                          (∀
                              (m :
                                Erdos390.Full.PaperBridgeFit.StructuredSampleData.Sample.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
                              LE.le.{0}
                                (Erdos390.Full.PaperBridgeFit.BaselineAllocation.baseWeight.{u_1}
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.baseline.{u_1, u_2} B) m)
                                (HDiv.hDiv.{0, 0, 0} Cactive
                                  (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B))) →
                            LE.le.{0}
                                (HAdd.hAdd.{0, 0, 0} Cfixed
                                  (HMul.hMul.{0, 0, 0}
                                    (Real.exp
                                      (HMul.hMul.{0, 0, 0} (2 : Real)
                                        (HMul.hMul.{0, 0, 0}
                                          (HAdd.hAdd.{0, 0, 0}
                                            (Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient C
                                              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                                                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)))
                                            (Erdos390.Full.PaperBridgeFit.BridgeData.nuisanceStatisticCoefficient.{u_1,
                                                u_2}
                                              B C))
                                          (HMul.hMul.{0, 0, 0} (3 : Real) ↑a))))
                                    Cactive))
                                (Erdos390.Full.PaperBridgeFit.BridgeData.L.{u_1, u_2} B) →
                              Erdos390.Full.PaperBridgeFit.BridgeData.HasPaperProposition87Conclusion.{u_1, u_2, u_4} B
                                Delta a markedTarget N Cpost fixedValue fixedWeight quota := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.hasPaperProposition87Conclusion_of_normalizedLawCompanion
