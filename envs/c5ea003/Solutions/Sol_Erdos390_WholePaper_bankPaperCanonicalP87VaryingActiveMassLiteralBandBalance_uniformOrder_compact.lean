-- Prove2me | solution 1 for Erdos390.WholePaper.bankPaperCanonicalP87VaryingActiveMassLiteralBandBalance_uniformOrder_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:39:46.117638+00:00
-- url     : https://prove2.me/submissions/65efa6f3-0429-4b1d-b304-8df5cc1c81c3

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
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_canonical_proposition87_compact
import Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_hasPaperProposition87Conclusion_of_normalizedLawCompanion


section
universe u_1 u_2
theorem Erdos390.Full.PaperBridgeFit.BridgeData.canonical_proposition87 : Erdos390.RemainingAnalyticGoal001_009.{u_1, u_2} := @Erdos390.Full.PaperBridgeFit.BridgeData.canonical_proposition87_compact
end
/- Source module: Erdos390.Full.PaperCanonicalNuisanceUniformFloor -/
section


/-!
# A root uniform lower floor for the canonical nuisance gap

The exact canonical nuisance gap is allowed to use a varying reference head
and a varying positive barycentric target.  This file bounds its two finite
dimensional constants by quantities depending only on the fixed head type,
and replaces the varying cell-mass margin by one prescribed positive floor.
The result is the uniform positive scalar needed before taking an eventual
Schur-smallness threshold.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus









namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual nuisance coordinate count is bounded by the full head count
plus the physical coordinate. -/
theorem nuisanceCoord_card_le_head_add_one :
    Fintype.card (NuisanceCoord B.HeadIndex) ≤ Fintype.card Head + 1 := by
  let f : NuisanceCoord B.HeadIndex → Option Head
    | .physical => none
    | .head h => some h.1
  have hf : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [f, Subtype.ext_iff]
  simpa using Fintype.card_le_of_injective f hf

theorem sqrt_nuisanceCoord_card_le_ceiling :
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) ≤
      nuisanceDimensionCeiling Head := by
  unfold nuisanceDimensionCeiling
  apply Real.sqrt_le_sqrt
  exact_mod_cast B.nuisanceCoord_card_le_head_add_one

theorem nuisanceStatisticCoefficient_le_ceiling
    {U : ℝ} (hU : 1 ≤ U) :
    B.nuisanceStatisticCoefficient U ≤
      nuisanceStatisticCoefficientCeiling Head U := by
  unfold nuisanceStatisticCoefficient nuisanceStatisticCoefficientCeiling
  have hmax : 0 ≤ max (PaperStatisticNorm.physicalLogCoefficient U)
      (3 / Real.log 2) := by
    exact (PaperStatisticNorm.physicalLogCoefficient_nonneg hU).trans
      (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right
    B.sqrt_nuisanceCoord_card_le_ceiling hmax







end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87SpeedRadius -/
section


/-!
# Noncircular speed, radius, and eventual slack choices for Proposition 8.7

These are purely quantitative closure lemmas.  All structural bounds are
fixed first; the effective ODE speed is their maximum, and the box radius is
four times that speed.  The ambient threshold is then increased.  No bound
is inferred from an already constructed path.
-/

open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open scoped BigOperators

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)







end BridgeData







/-- Once all constants and the radius are fixed, the logarithmic ambient
slack inequality used by the feasibility ledger holds eventually. -/
theorem eventually_fixed_exponential_slack_le_L
    (Cfixed K Cactive : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Cfixed + Real.exp K * Cactive ≤ Scale.L n := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hLTop.eventually
    (eventually_ge_atTop (Cfixed + Real.exp K * Cactive))

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87CanonicalFeasibilitySlackEventually -/
section


/-!
# Canonical eventual feasibility slack for Proposition 8.7

The finite ODE assembly asks for an exponential feasibility inequality whose
nuisance coefficient is attached to the current canonical bridge data.  The
coefficient is uniformly bounded by the head-cardinality ceiling.  Therefore,
after `W`, the head type, and the effective ball have been fixed, the required
inequality follows from `L(n) -> infinity`; it is not an analytic hypothesis
at the final Proposition 8.7 call site.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel PaperGuardCensus

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Uniform eventual form of the literal feasibility slack used by the
canonical ODE assembly. -/
theorem eventually_canonical_exponential_slack_le_L
    (U : ℝ) (hU : 1 ≤ U) (W : ℕ) (a : NNReal)
    (Cfixed Cactive : ℝ) (hCactive : 0 ≤ Cactive) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Cfixed +
            Real.exp (2 *
              ((PaperStatisticNorm.valuationLogCoefficient
                    U B.sampleData.W +
                  B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
              Cactive ≤ B.L := by
  let Kceiling : ℝ :=
    2 * ((PaperStatisticNorm.valuationLogCoefficient U W +
      nuisanceStatisticCoefficientCeiling Head U) * (3 * (a : ℝ)))
  have hlarge := eventually_fixed_exponential_slack_le_L
    Cfixed Kceiling Cactive
  filter_upwards [hlarge] with n hlargeN
  intro B hBn hBW
  have hcoeff :
      PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U ≤
        PaperStatisticNorm.valuationLogCoefficient U W +
          nuisanceStatisticCoefficientCeiling Head U := by
    rw [hBW]
    linarith [B.nuisanceStatisticCoefficient_le_ceiling hU]
  have hscaleNonneg : 0 ≤ 3 * (a : ℝ) := by positivity
  have hexponent :
      2 * ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ))) ≤
        Kceiling := by
    dsimp only [Kceiling]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hscaleNonneg]
  have hexp :
      Real.exp (2 *
          ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
            B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) ≤
        Real.exp Kceiling := Real.exp_le_exp.mpr hexponent
  have hscaled := mul_le_mul_of_nonneg_right hexp hCactive
  calc
    Cfixed +
          Real.exp (2 *
            ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
              B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
            Cactive ≤
        Cfixed + Real.exp Kceiling * Cactive :=
      by linarith
    _ ≤ B.L := by
      change Cfixed + Real.exp Kceiling * Cactive ≤
        Scale.L B.sampleData.n
      rw [hBn]
      exact hlargeN

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperProposition87LiteralBandBalance -/
section


/-!
# Literal residual-balance form of paper Proposition 8.7

The generalized Proposition 8.7 engine takes a prescribed vector of band
moment increments.  In the paper that vector is not arbitrary: its `j`th
coordinate is the initial sum of the marked residuals in the `j`th prime
band.  This file records that specialization and derives the displayed
post-fit identity `sum_{p in P_j} r_p = 0` exactly at finite `n`.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)



/-- A band-score moment is exactly the sum of its marked valuation moments.
This is a finite identity, with no asymptotic or squarefree replacement. -/
theorem paperMoment_bandScore_eq_sum_markedValuation [Nonempty Head]
    (xi : B.ParamSpace) (j : Band) :
    B.paperMoment (B.bandScore j) xi =
      ∑ p ∈ B.partition.data.fiber j,
        B.paperMoment (B.markedValuation p.1) xi := by
  simp only [paperMoment, bandScore, markedValuation,
    FiniteExponentialFamily.moment, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- If `Delta` is the initial band-residual vector and the endpoint changes
each band moment by `Delta`, then every endpoint band residual is exactly
zero. -/
theorem markedBandResidual_eq_zero_of_bandMoment_increment
    [Nonempty Head]
    (Delta : Band → ℝ) (markedTarget : ℕ → ℝ)
    (xi0 xi1 : B.ParamSpace)
    (hDelta : ∀ j, Delta j = B.markedBandResidual markedTarget xi0 j)
    (hbands : ∀ j,
      B.paperMoment (B.bandScore j) xi1 =
        B.paperMoment (B.bandScore j) xi0 + Delta j) :
    ∀ j, B.markedBandResidual markedTarget xi1 j = 0 := by
  intro j
  rw [markedBandResidual, Finset.sum_sub_distrib,
    ← B.paperMoment_bandScore_eq_sum_markedValuation xi1 j,
    hbands j, hDelta j, markedBandResidual,
    Finset.sum_sub_distrib,
    ← B.paperMoment_bandScore_eq_sum_markedValuation xi0 j]
  ring





/-- Upgrade the generalized finite-fit endpoint to the literal residual form
used in the paper. -/
theorem hasPaperProposition87Conclusion_of_fit
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (Delta : Band → ℝ) (a : NNReal)
    (markedTarget : ℕ → ℝ) (N Cpost : ℝ)
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ)
    (hDelta : ∀ j,
      Delta j = B.markedBandResidual markedTarget 0 j)
    (hfit : B.HasPhysicallyCenteredFixedPartitionFit Delta a
      (ArithmeticModel.primeBand B.sampleData.n B.sampleData.W)
      markedTarget N Cpost fixedValue fixedWeight quota) :
    B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
      fixedValue fixedWeight quota := by
  unfold HasPhysicallyCenteredFixedPartitionFit at hfit
  obtain ⟨path, hpath⟩ := hfit
  refine ⟨path, ?_, ?_⟩
  · exact hpath
  · exact B.markedBandResidual_eq_zero_of_bandMoment_increment
      Delta markedTarget 0 (path 1) hDelta hpath.2.2.2.2.1

end BridgeData

open ArithmeticModel PaperGuardCensus PaperPermittedRegularMesh
open RegularMeshPrimeCutoffs



namespace BridgeData

/-- Assumption-free literal paper terminal.  It specializes the generalized
engine to the full arithmetic prime band and closes the displayed exact
band-residual equations. -/
theorem canonical_proposition87_literalBandBalance
    (cMesh : ℝ)
    (I : PhysicalIntervals) (U : ℝ)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) :
    CanonicalProposition87LiteralBalanceStatement
      cMesh I U Cprom Cbank ledger := by
  have hgeneral := canonical_proposition87 cMesh I U Cprom Cbank ledger
  unfold CanonicalProposition87Statement at hgeneral
  unfold CanonicalProposition87LiteralBalanceStatement
  intro hcMesh hU hlowerOne hupperU
  obtain ⟨meshTol, hmeshTol, W₀, hWgeneral⟩ :=
    hgeneral hcMesh hU hlowerOne hupperU
  refine ⟨meshTol, hmeshTol, W₀, ?_⟩
  intro W hW Head _instHeadFintype _instHeadDecidable _instHeadNonempty
    Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive marginFloor
    hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  obtain ⟨a, ha, Cpost, hCpost, hMeshGeneral⟩ :=
    hWgeneral W hW Phead hPhead Ctarget Cinitial Cmass Cfixed Cactive
      marginFloor hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  refine ⟨a, ha, Cpost, hCpost, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  have hEventual := hMeshGeneral M hdelta hPermitted hfine
  filter_upwards [hEventual] with n hn
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline Delta henv markedTarget N hN hqMass
    hinitialMarked hDelta Fixed _instFixedFintype fixedValue fixedWeight
    quota hquota hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  have hfit := hn B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hTmargin hbaseline Delta henv
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p hp ↦ prime_of_mem_primeBand hp)
    (fun p hp ↦ le_yNat_of_mem_primeBand hp)
    markedTarget N hN hqMass hinitialMarked fixedValue fixedWeight quota
    hquota hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  exact B.hasPaperProposition87Conclusion_of_fit Delta a markedTarget N Cpost
    fixedValue fixedWeight quota hDelta hfit

end BridgeData

end

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













/-- The two exact canonical target-envelope hypotheses are invariant under
the same normalization of the raw requested increments. -/
theorem hasTargetEnvelopes_normalizedLawCompanion
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    {C : Real} (Delta : Band -> Real)
    (henv : B.HasTargetEnvelopes C Delta) :
    (B.normalizedLawCompanion T).HasTargetEnvelopes C
      (fun j => Delta j / q) := by
  rcases henv with ⟨hband, hslow⟩
  constructor
  · intro j
    have hj := hband j
    rw [B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline] at hj
    rw [abs_div, abs_of_pos hq,
      B.normalizedLawCompanion_q, B.normalizedLawCompanion_L]
    apply (div_le_iff₀ hq).2
    calc
      abs (Delta j) <=
          (q / B.L) * C * abs (B.harmonicMass j) := hj
      _ = ((1 / B.L) * C * abs (B.harmonicMass j)) * q := by ring
  · have hs := hslow
    rw [B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline] at hs
    rw [B.normalizedLawCompanion_q, B.normalizedLawCompanion_L,
      B.normalizedLawCompanion_w]
    have hcenter : ∀ j : Band,
        (B.normalizedLawCompanion T).bandCenter j = B.bandCenter j := by
      intro j
      rfl
    simp_rw [hcenter]
    have hsum :
        (∑ j : Band, B.bandCenter j * (Delta j / q)) =
          (∑ j : Band, B.bandCenter j * Delta j) / q := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum, abs_div, abs_of_pos hq]
    apply (div_le_iff₀ hq).2
    calc
      abs (∑ j : Band, B.bandCenter j * Delta j) <=
          (q / B.L) * C * B.w := hs
      _ = ((1 / B.L) * C * B.w) * q := by ring

/-- A literal `Cactive/L` coordinate ledger becomes the corresponding
mass-one `(Cactive/q)/L` ledger.  This is a consequence, not an additional
input. -/
theorem normalizedLawCompanion_baseWeight_le_div_log
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    {Cactive : Real}
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L) :
    forall m : B.sampleData.Sample,
      (B.normalizedLawCompanion T).baseline.baseWeight m <=
        (Cactive / q) / (B.normalizedLawCompanion T).L := by
  intro m
  have hm := hactive m
  rw [B.baseWeight_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline m] at hm
  rw [B.normalizedLawCompanion_L]
  calc
    (B.normalizedLawCompanion T).baseline.baseWeight m <=
        (Cactive / B.L) / q := by
      apply (le_div_iff₀ hq).2
      simpa only [mul_comm] using hm
    _ = (Cactive / q) / B.L := by ring

/-- The usual active-mass majorant becomes the mass-one majorant after
normalizing `N` by the same factor. -/
theorem normalizedLawCompanion_q_le_of_activeMass_bound
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    {Cmass N : Real}
    (hqMass : q <= Cmass * N) :
    (B.normalizedLawCompanion T).q <= Cmass * (N / q) := by
  rw [B.normalizedLawCompanion_q]
  calc
    (1 : Real) <= (Cmass * N) / q :=
      (le_div_iff₀ hq).2 (by simpa only [one_mul] using hqMass)
    _ = Cmass * (N / q) := by ring

/-- The initial marked-prime rate is homogeneous under simultaneous
normalization of the marked target, moment, and ambient scale `N`. -/
theorem normalizedLawCompanion_initialMarkedRate
    [Nonempty Head]
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq)
    (markedTarget : Nat -> Real) (N Cinitial : Real)
    (primes : Finset Nat)
    (hinitial : ∀ p ∈ primes,
      abs (markedTarget p - B.paperMoment (B.markedValuation p) 0) <=
        Cinitial * N / ((p : Real) * B.L)) :
    ∀ p ∈ primes,
      abs (markedTarget p / q -
          (B.normalizedLawCompanion T).paperMoment
            ((B.normalizedLawCompanion T).markedValuation p) 0) <=
        Cinitial * (N / q) /
          ((p : Real) * (B.normalizedLawCompanion T).L) := by
  intro p hp
  have hpRaw := hinitial p hp
  rw [B.paperMoment_eq_activeMass_mul_normalizedLawCompanion
    T q hq hbaseline] at hpRaw
  have hidentity : markedTarget p / q -
        (B.normalizedLawCompanion T).paperMoment
          ((B.normalizedLawCompanion T).markedValuation p) 0 =
      (markedTarget p - q *
        (B.normalizedLawCompanion T).paperMoment
          ((B.normalizedLawCompanion T).markedValuation p) 0) / q := by
    field_simp [ne_of_gt hq]
  rw [hidentity, abs_div, abs_of_pos hq,
    B.normalizedLawCompanion_L]
  apply (div_le_iff₀ hq).2
  calc
    abs (markedTarget p - q *
        (B.normalizedLawCompanion T).paperMoment
          ((B.normalizedLawCompanion T).markedValuation p) 0) <=
      Cinitial * N / ((p : Real) * B.L) := hpRaw
    _ = (Cinitial * (N / q) / ((p : Real) * B.L)) * q := by
      have hcancel : q * (N / q) = N := by
        field_simp [ne_of_gt hq]
      rw [show (Cinitial * (N / q) / ((p : Real) * B.L)) * q =
          (q * (N / q)) *
            (Cinitial / ((p : Real) * B.L)) by ring,
        hcancel]
      ring





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



/-- Canonically named public endpoint of the homogeneous transport.  Its
type is exactly the preceding theorem: normalized-law canonical P87 data
produce the literal active-mass P87 conclusion with the physical frozen
layer and integer quota. -/
alias canonical_activeMass_proposition87_of_normalizedLawCompanion :=
  hasPaperProposition87Conclusion_of_normalizedLawCompanion

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

/- Source module: Erdos390.WholePaper.BankPaperCanonicalP87VaryingMassUniformOrderConnector -/
section


/-!
# Uniform paper order for varying-mass canonical Proposition 8.7

The varying-active-mass Proposition 8.7 theorem is uniform in the mass
family once that family is eventually at least one.  Its original public
statement, however, takes the family before exposing the mesh threshold and
the prime cutoff, so that logical statement does not record the uniform
dependency order.

This connector exposes `meshTol` and `W0` first.  Only after a width
`W ≥ W0` has been selected is the varying family `qMass` introduced.  The
proof uses the mass-one literal theorem to select the two uniform cutoffs,
then repeats the normalized-law transport used by
`canonical_proposition87_varyingActiveMassLiteralBandBalance`.
-/

open Filter Topology
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperBridgeFit.BridgeData
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section



set_option maxHeartbeats 4000000 in
/-- Varying-active-mass canonical Proposition 8.7 with its mesh tolerance
and prime cutoff selected uniformly before the final width and mass family.
-/
theorem
    bankPaperCanonicalP87VaryingActiveMassLiteralBandBalance_uniformOrder
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : ∀ n, Ledger n Cprom Cbank) :
    BankPaperCanonicalP87VaryingMassUniformOrderStatement
      cMesh I U Cprom Cbank ledger := by
  have hold := canonical_proposition87_literalBandBalance
    cMesh I U Cprom Cbank ledger
  unfold CanonicalProposition87LiteralBalanceStatement at hold
  unfold BankPaperCanonicalP87VaryingMassUniformOrderStatement
  intro hcMesh hU hlowerOne hupperU
  obtain ⟨meshTol, hmeshTol, Wold, hWold⟩ :=
    hold hcMesh hU hlowerOne hupperU
  let W0 : Nat := max Wold 2
  refine ⟨meshTol, hmeshTol, W0, ?_⟩
  intro W hW qMass hqOne Head _instHeadFintype _instHeadDecidable
    _instHeadNonempty Phead hPhead
    Ctarget Cinitial Cmass Cfixed Cactive marginFloor
    hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  have hWoldLe : Wold ≤ W := (le_max_left Wold 2).trans hW
  have hWtwo : 2 ≤ W := (le_max_right Wold 2).trans hW
  obtain ⟨radius, hradius, Cpost, hCpost, hMeshOld⟩ :=
    hWold W hWoldLe Phead hPhead
      Ctarget Cinitial Cmass Cfixed Cactive marginFloor
      hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  refine ⟨radius, hradius, Cpost, hCpost, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  have hOldN := hMeshOld M hdelta hPermitted hfine
  have hSlackN := eventually_canonical_exponential_slack_le_L
    (Head := Head) (Band := Fin (M.cellCount + 1))
    U hU W radius Cfixed Cactive hCactive
  filter_upwards [hOldN, hSlackN, hqOne] with n hnOld hslack hqOneN
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hq hTmargin hbaseline Delta henv markedTarget N hN hMassBound
    hinitial hDelta Fixed _instFixedFintype fixedValue fixedWeight
    quota hquota hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  let q : Real := qMass B.sampleData.n
  let B0 := B.normalizedLawCompanion T
  have hqOneB : 1 ≤ q := by
    dsimp only [q]
    rw [hBn]
    exact hqOneN
  have hqPos : 0 < q := lt_of_lt_of_le zero_lt_one hqOneB
  have hqProof : hq = hqPos := Subsingleton.elim _ _
  have hbaseline' : B.baseline = T.activeMassBaseline q hqPos := by
    simpa only [q, hqProof] using hbaseline
  have hBWlarge : 1 < B.sampleData.W := by
    rw [hBW]
    omega
  have hhiIntervals : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiU : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound U B.sampleData.n := by
    intro sigma
    rw [hhiIntervals]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperU sigma) B.sampleData.n
  have henv0 := B.hasTargetEnvelopes_normalizedLawCompanion
    T q hqPos hbaseline' Delta henv
  have hN0 : 0 ≤ N / q := div_nonneg hN hqPos.le
  have hqRaw : q ≤ Cmass * N := by
    rw [← B.q_eq_of_baseline_eq_activeMassBaseline
      T q hqPos hbaseline']
    exact hMassBound
  have hqMass0 : B0.q ≤ Cmass * (N / q) := by
    exact B.normalizedLawCompanion_q_le_of_activeMass_bound
      T q hqPos hqRaw
  have hinitial0 := B.normalizedLawCompanion_initialMarkedRate
    T q hqPos hbaseline' markedTarget N Cinitial
      (primeBand B.sampleData.n B.sampleData.W) hinitial
  have hDelta0 : ∀ j,
      Delta j / q = B0.markedBandResidual
        (fun p => markedTarget p / q) 0 j := by
    intro j
    have hres :=
      B.markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
        T q hqPos hbaseline' markedTarget 0 j
    rw [hDelta j, hres]
    field_simp [ne_of_gt hqPos]
    ring
  have hactive0Raw := B.normalizedLawCompanion_baseWeight_le_div_log
    T q hqPos hbaseline' hactiveLedger
  have hCdiv : Cactive / q ≤ Cactive :=
    div_le_self hCactive hqOneB
  have hactive0 : ∀ m : B0.sampleData.Sample,
      B0.baseline.baseWeight m ≤ Cactive / B0.L := by
    intro m
    exact (hactive0Raw m).trans
      (div_le_div_of_nonneg_right hCdiv B.L_pos.le)
  have hfrozen0 : ∀ x : Nat,
      frozenAmbientWeight (fun e : Fin 0 => Fin.elim0 e)
        (fun e : Fin 0 => Fin.elim0 e) x ∈ Set.Icc (0 : Real) 1 := by
    intro x
    simp [frozenAmbientWeight]
  have hfrozenLedger0 : ∀ m : B0.sampleData.Sample,
      frozenAmbientWeight (fun e : Fin 0 => Fin.elim0 e)
        (fun e : Fin 0 => Fin.elim0 e) (B0.sampleData.value m) ≤
          Cfixed / B0.L := by
    intro m
    simp only [frozenAmbientWeight, Finset.univ_eq_empty,
      Finset.sum_empty]
    exact div_nonneg hCfixed B0.L_pos.le
  have hquota0 : ((1 : Int) : Real) =
      (∑ e : Fin 0, (Fin.elim0 e : Real)) + B0.q := by
    simp [B0, normalizedLawCompanion_q]
  have Hnormalized : B0.HasPaperProposition87Conclusion
      (fun j => Delta j / q) radius (fun p => markedTarget p / q)
      (N / q) Cpost (fun e : Fin 0 => Fin.elim0 e)
      (fun e : Fin 0 => Fin.elim0 e) 1 := by
    exact hnOld B0 hBn hBW hsep hremaining
      (by simpa only [B0, normalizedLawCompanion] using hcanonical)
      (by simpa only [B0, normalizedLawCompanion] using hpartition)
      (by simpa only [B0, normalizedLawCompanion] using hscale)
      T hTmargin rfl (fun j => Delta j / q) henv0
      (fun p => markedTarget p / q) (N / q) hN0 hqMass0
      (by simpa only [B0, normalizedLawCompanion] using hinitial0)
      hDelta0 (fun e : Fin 0 => Fin.elim0 e)
      (fun e : Fin 0 => Fin.elim0 e) 1 hquota0
      (by simpa only [B0, normalizedLawCompanion] using hheadSeparated)
      hfrozen0 hfrozenLedger0 hactive0
  exact B.canonical_activeMass_proposition87_of_normalizedLawCompanion
    T q hqPos hbaseline' Delta radius markedTarget N Cpost
    (fun e : Fin 0 => Fin.elim0 e) (fun e : Fin 0 => Fin.elim0 e) 1
    Hnormalized fixedValue fixedWeight quota hquota hU hBWlarge hhiU
    hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
    (hslack B hBn hBW)

end

end Erdos390.WholePaper

end

universe u_1 u_2
theorem solution : Erdos390.RemainingAnalyticGoal008_003.{u_1, u_2} := by
  exact @Erdos390.WholePaper.bankPaperCanonicalP87VaryingActiveMassLiteralBandBalance_uniformOrder
