-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:53.026718+00:00
-- url     : https://prove2.me/submissions/50814475-8ee5-42c2-9026-f1050a12bbb9

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Theorems.Thm_Erdos390_WholePaper_finiteAsymmetricLocalLemma_conditionalBound
import Theorems.Thm_Erdos390_WholePaper_tangentOrderedPairEndpointBudget_div_le_densityCoefficients_compact


section
universe u_1
theorem Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_densityCoefficients : Erdos390.RemainingAnalyticGoal008_039.{u_1} := @Erdos390.WholePaper.tangentOrderedPairEndpointBudget_div_le_densityCoefficients_compact
end
/- Source module: Erdos390.WholePaper.TangentStarTransport -/
section


/-!
# Exact finite star transport for tangent residuals

A zero-sum residual on a finite vertex type is transported through one
chosen pivot.  Positive residual leaves its vertex for the pivot; negative
residual is supplied from the pivot.  The construction is literal,
nonnegative, supported on the star, and has exactly the requested
divergence.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







variable {V : Type*} [DecidableEq V]

/-! ## Pointwise support and sign -/











/-! ## Exact outgoing and incoming sums -/

variable [Fintype V]















/-! ## Traffic -/





/-! ## Boundary identities consumed by `TangentFlowAlgebra` -/

/-- Finite integration by parts for any directed flow. -/
theorem tangentFlow_weightedBoundary_eq_divergence
    {W : Type*} [Fintype W]
    (flow : W → W → ℝ) (value : W → ℝ) :
    (∑ source : W, ∑ target : W,
        flow source target * (value source - value target)) =
      ∑ v : W, tangentFlowDivergence flow v * value v := by
  classical
  have hout :
      (∑ source : W, ∑ target : W,
          flow source target * value source) =
        ∑ source : W,
          (∑ target : W, flow source target) * value source := by
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.sum_mul]
  have hin :
      (∑ source : W, ∑ target : W,
          flow source target * value target) =
        ∑ target : W,
          (∑ source : W, flow source target) * value target := by
    calc
      (∑ source : W, ∑ target : W,
          flow source target * value target) =
          ∑ target : W, ∑ source : W,
            flow source target * value target := by
        rw [Finset.sum_comm]
      _ = ∑ target : W,
          (∑ source : W, flow source target) * value target := by
        apply Finset.sum_congr rfl
        intro target _htarget
        rw [Finset.sum_mul]
  calc
    (∑ source : W, ∑ target : W,
        flow source target * (value source - value target)) =
        (∑ source : W, ∑ target : W,
          flow source target * value source) -
        ∑ source : W, ∑ target : W,
          flow source target * value target := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ source : W,
          (∑ target : W, flow source target) * value source) -
        ∑ target : W,
          (∑ source : W, flow source target) * value target := by
      rw [hout, hin]
    _ = ∑ v : W, tangentFlowDivergence flow v * value v := by
      simp only [tangentFlowDivergence, sub_mul,
        Finset.sum_sub_distrib]









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FiniteAsymmetricLocalLemma -/
section


/-!
# The finite asymmetric Lovasz local lemma

This file proves the standard finite asymmetric local lemma directly on a
probability space.  The dependency hypothesis is stated as the exact measure
factorization that the proof uses: a bad event is independent of every finite
intersection of complements indexed by non-neighbors.

The key theorem `finiteAsymmetricLocalLemma_conditionalBound` is the genuine
conditional-probability induction.  For every finite conditioning family not
containing `i`, it proves

`P(A i | all events in the family are avoided) <= x i`

in denominator-free form.  It does not assume this conditional estimate.
The final induction then gives the usual positive product lower bound for the
probability that all bad events are avoided.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





/-- Adding one index removes its bad event from the event already being
conditioned on. -/
theorem avoidEvents_insert {I Omega : Type*} [DecidableEq I]
    (A : I -> Set Omega) (i : I) (s : Finset I) :
    avoidEvents A (insert i s) = avoidEvents A s \ A i := by
  simp [avoidEvents, Set.diff_eq, Set.inter_comm]





/-!
## The conditional-probability induction

For a fixed event `i` and conditioning set `s`, split `s` into the neighbors
of `i` and the non-neighbors of `i`.  Independence removes the latter.  The
strong induction hypothesis is then applied successively while the neighbors
are inserted.  This proves the denominator lower bound required to cancel
the neighborhood product in the asymmetric-LLL hypothesis.
-/



/-!
## Product lower bound and the local lemma
-/

/-- Every finite avoidance event has at least the standard product lower
bound. -/
theorem finiteAsymmetricLocalLemma_lowerBound
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ avoidEvents A s) =
        mu.real (A i) * mu.real (avoidEvents A s))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    ∀ s : Finset I,
      (∏ i ∈ s, (1 - x i)) ≤ mu.real (avoidEvents A s) := by
  classical
  have hconditional := finiteAsymmetricLocalLemma_conditionalBound
    mu A Gamma x hA hx hindep hprobability
  intro s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hrec =>
      have hbound := hconditional s a ha
      have hbound' :
          mu.real (avoidEvents A s ∩ A a) ≤
            x a * mu.real (avoidEvents A s) := by
        simpa only [Set.inter_comm] using hbound
      have hsplit := measureReal_inter_add_diff
        (μ := mu) (s := avoidEvents A s) (t := A a) (hA a)
      have hstep :
          (1 - x a) * mu.real (avoidEvents A s) ≤
            mu.real (avoidEvents A s \ A a) := by
        nlinarith [hbound', hsplit]
      have hfactorNonneg : 0 ≤ 1 - x a :=
        sub_nonneg.mpr (le_of_lt (hx a).2)
      calc
        (∏ i ∈ insert a s, (1 - x i)) =
            (1 - x a) * ∏ i ∈ s, (1 - x i) := by
              rw [Finset.prod_insert ha]
        _ ≤ (1 - x a) * mu.real (avoidEvents A s) :=
              mul_le_mul_of_nonneg_left hrec hfactorNonneg
        _ ≤ mu.real (avoidEvents A s \ A a) := hstep
        _ = mu.real (avoidEvents A (insert a s)) :=
              congrArg mu.real (avoidEvents_insert A a s).symm

/-- The event avoiding every bad event has strictly positive probability. -/
theorem finiteAsymmetricLocalLemma_positive
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ avoidEvents A s) =
        mu.real (A i) * mu.real (avoidEvents A s))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    0 < mu.real (avoidEvents A Finset.univ) := by
  have hlower := finiteAsymmetricLocalLemma_lowerBound
    mu A Gamma x hA hx hindep hprobability Finset.univ
  have hproductPositive :
      0 < ∏ i ∈ (Finset.univ : Finset I), (1 - x i) := by
    apply Finset.prod_pos
    intro i _hi
    exact sub_pos.mpr (hx i).2
  exact hproductPositive.trans_le hlower



/-- Consequently, the event avoiding every bad event is nonempty. -/
theorem finiteAsymmetricLocalLemma_nonempty
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ avoidEvents A s) =
        mu.real (A i) * mu.real (avoidEvents A s))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    (avoidEvents A Finset.univ).Nonempty := by
  apply nonempty_of_measureReal_ne_zero
  exact (finiteAsymmetricLocalLemma_positive
    mu A Gamma x hA hx hindep hprobability).ne'



/-- Existential form of the finite asymmetric Lovasz local lemma. -/
theorem finiteAsymmetricLocalLemma
    {I Omega : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : I -> Set Omega) (Gamma : I -> Finset I) (x : I -> Real)
    (hA : ∀ i, MeasurableSet (A i))
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hindep : ∀ (i : I) (s : Finset I), i ∉ s ->
      Disjoint s (Gamma i) ->
      mu.real (A i ∩ avoidEvents A s) =
        mu.real (A i) * mu.real (avoidEvents A s))
    (hprobability : ∀ i,
      mu.real (A i) ≤
        x i * ∏ j ∈ Gamma i, (1 - x j)) :
    ∃ omega : Omega, ∀ i : I, omega ∉ A i := by
  obtain ⟨omega, homega⟩ := finiteAsymmetricLocalLemma_nonempty
    mu A Gamma x hA hx hindep hprobability
  refine ⟨omega, ?_⟩
  simpa [avoidEvents] using homega

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentLLLNumerics -/
section


/-!
# Numerical bookkeeping for the tangent-stage local lemma

The collision argument uses only one deterministic product estimate before
the asymmetric Lovasz local lemma is invoked.  For numbers in the unit
interval, the product of their complements is at least one minus their sum.
Consequently, if the doubled probability mass in every dependency
neighborhood is at most one half, the choice `x_E = 2 * P(E)` satisfies the
entire numerical inequality required by the asymmetric local lemma.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Finite union-bound product inequality in the precise orientation used by
the asymmetric local lemma. -/
theorem one_sub_sum_le_prod_one_sub
    {I : Type*} (s : Finset I) (x : I → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hxa := hx a (Finset.mem_insert_self a s)
      have hxs : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 := by
        intro i hi
        exact hx i (Finset.mem_insert_of_mem hi)
      have hsumNonneg : 0 ≤ ∑ i ∈ s, x i := by
        exact Finset.sum_nonneg fun i hi ↦ (hxs i hi).1
      have hbase :
          1 - (x a + ∑ i ∈ s, x i) ≤
            (1 - x a) * (1 - ∑ i ∈ s, x i) := by
        nlinarith
      have hmul :
          (1 - x a) * (1 - ∑ i ∈ s, x i) ≤
            (1 - x a) * ∏ i ∈ s, (1 - x i) :=
        mul_le_mul_of_nonneg_left (ih hxs) (sub_nonneg.mpr hxa.2)
      simpa only [Finset.sum_insert ha, Finset.prod_insert ha] using
        hbase.trans hmul

/-- If a finite family of nonnegative numbers has sum at most one half,
then the product of their doubled complements is at least one half. -/
theorem half_le_prod_one_sub_two_mul
    {I : Type*} [DecidableEq I]
    (s : Finset I) (probability : I → ℝ)
    (hprobability : ∀ i ∈ s, 0 ≤ probability i)
    (hmass : ∑ i ∈ s, 2 * probability i ≤ 1 / 2) :
    1 / 2 ≤ ∏ i ∈ s, (1 - 2 * probability i) := by
  have hterm : ∀ i ∈ s, 0 ≤ 2 * probability i ∧
      2 * probability i ≤ 1 := by
    intro i hi
    have hnonneg : 0 ≤ 2 * probability i := by
      exact mul_nonneg (by norm_num) (hprobability i hi)
    have hleSum : 2 * probability i ≤
        ∑ j ∈ s, 2 * probability j := by
      exact Finset.single_le_sum
        (fun j hj ↦ mul_nonneg (by norm_num) (hprobability j hj)) hi
    exact ⟨hnonneg, hleSum.trans (hmass.trans (by norm_num))⟩
  have hprod := one_sub_sum_le_prod_one_sub s
    (fun i ↦ 2 * probability i) hterm
  linarith

/-- The factor-two/factor-four bookkeeping used in the paper: neighborhood
mass at most `1/8` gives doubled `x`-mass at most `1/2`, and hence the
asymmetric-LLL inequality for the distinguished event. -/
theorem probability_le_two_mul_probability_mul_neighborProduct
    {I : Type*} [DecidableEq I]
    (neighbors : Finset I) (probability : I → ℝ)
    (event : I)
    (hprobability : ∀ i ∈ insert event neighbors,
      0 ≤ probability i)
    (hneighborhood : ∑ i ∈ neighbors, probability i ≤ 1 / 4) :
    probability event ≤
      (2 * probability event) *
        ∏ i ∈ neighbors, (1 - 2 * probability i) := by
  have hneighborNonneg : ∀ i ∈ neighbors, 0 ≤ probability i := by
    intro i hi
    exact hprobability i (Finset.mem_insert_of_mem hi)
  have hdoubleMass : ∑ i ∈ neighbors, 2 * probability i ≤ 1 / 2 := by
    rw [← Finset.mul_sum]
    nlinarith
  have hprod := half_le_prod_one_sub_two_mul neighbors probability
    hneighborNonneg hdoubleMass
  have heventNonneg : 0 ≤ probability event :=
    hprobability event (Finset.mem_insert_self event neighbors)
  nlinarith [mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2 * probability event by positivity)]

/-- Paper-facing form.  A per-request collision sum at most `1/8` bounds a
bad event's dependency-neighborhood probability mass by `1/4`, so the
previous theorem applies verbatim. -/
theorem probability_le_two_mul_probability_mul_neighborProduct_of_requestMass
    {I : Type*} [DecidableEq I]
    (neighbors : Finset I) (probability : I → ℝ)
    (event : I)
    (hprobability : ∀ i ∈ insert event neighbors,
      0 ≤ probability i)
    (requestMass : ℝ)
    (hrequestMass : requestMass ≤ 1 / 8)
    (hneighborhood : ∑ i ∈ neighbors, probability i ≤
      2 * requestMass) :
    probability event ≤
      (2 * probability event) *
        ∏ i ∈ neighbors, (1 - 2 * probability i) := by
  apply probability_le_two_mul_probability_mul_neighborProduct
    neighbors probability event hprobability
  nlinarith

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentRequestSplitting -/
section


/-!
# Literal finite splitting of tangent-flow requests

This file formalizes only the algebra in the paper's request splitting.
It assumes concrete nonnegative edge masses and forms explicit `Fin k`
families of equal pieces.  It contains no flow-existence, list-capacity,
or collision-avoidance assertion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem one_le_tangentRequestCount (L sigma f : ℝ) :
    1 ≤ tangentRequestCount L sigma f := by
  exact le_max_left 1 (Nat.ceil (4 * L * f / sigma))

theorem tangentRequestCount_pos (L sigma f : ℝ) :
    0 < tangentRequestCount L sigma f := by
  exact lt_of_lt_of_le Nat.zero_lt_one (one_le_tangentRequestCount L sigma f)







/-- The request count is at most normalized mass plus one.  Equality can
occur at `f=0`, so the globally valid form is non-strict. -/
theorem cast_tangentRequestCount_le
    {L sigma f : ℝ} (hf : 0 ≤ f) (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentRequestCount L sigma f : ℝ) ≤
      4 * L * f / sigma + 1 := by
  have hnormalized : 0 ≤ 4 * L * f / sigma := by positivity
  have hceil : (Nat.ceil (4 * L * f / sigma) : ℝ) ≤
      4 * L * f / sigma + 1 :=
    (Nat.ceil_lt_add_one hnormalized).le
  have hone : (1 : ℝ) ≤ 4 * L * f / sigma + 1 := by
    linarith
  unfold tangentRequestCount
  push_cast
  exact max_le hone hceil



/-- The `Fin k` equal pieces of one edge sum exactly to its original mass. -/
theorem sum_tangentRequestPieceMass
    (L sigma f : ℝ) :
    (∑ _i : Fin (tangentRequestCount L sigma f),
        tangentRequestPieceMass L sigma f) = f := by
  have hk : (tangentRequestCount L sigma f : ℝ) ≠ 0 := by
    exact_mod_cast (tangentRequestCount_pos L sigma f).ne'
  simp only [tangentRequestPieceMass, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp





























/-- Request splitting preserves the complete directed edge boundary when
tested against any label function.  This is the exact bridge from the
paper's edge flow to the request family consumed by `tangentUpdate`. -/
theorem sum_tangentSplitRequestWeight_mul_sub
    {E P : Type*} (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (value : P → ℝ) :
    (∑ request : TangentSplitRequest edges L sigma flow,
        tangentSplitRequestWeight request *
          (value (tangentSplitRequestSource source request) -
            value (tangentSplitRequestTarget target request))) =
      ∑ e ∈ edges, flow e * (value (source e) - value (target e)) := by
  classical
  simp only [TangentSplitRequest, tangentSplitRequestWeight,
    tangentSplitRequestSource, tangentSplitRequestTarget,
    tangentSplitRequestEdge, Fintype.sum_sigma]
  calc
    (∑ e : ↑edges,
        ∑ _i : Fin (tangentRequestCount L sigma (flow e.1)),
          tangentRequestPieceMass L sigma (flow e.1) *
            (value (source e.1) - value (target e.1))) =
      ∑ e : ↑edges,
        flow e.1 * (value (source e.1) - value (target e.1)) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [← Finset.sum_mul, sum_tangentRequestPieceMass]
    _ = ∑ e ∈ edges,
        flow e * (value (source e) - value (target e)) := by
      simpa using Finset.sum_attach edges
        (fun e ↦ flow e * (value (source e) - value (target e)))



/-- Literal finite form of the total request-count estimate. -/
theorem cast_tangentRequestTotal_le
    {E : Type*} (edges : Finset E) {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentRequestTotal edges L sigma flow : ℝ) ≤
      (4 * L / sigma) * (∑ e ∈ edges, flow e) + edges.card := by
  classical
  unfold tangentRequestTotal
  push_cast
  calc
    (∑ e ∈ edges, (tangentRequestCount L sigma (flow e) : ℝ)) ≤
        ∑ e ∈ edges, (4 * L * flow e / sigma + 1) := by
      apply Finset.sum_le_sum
      intro e he
      exact cast_tangentRequestCount_le (hflow e he) hL hsigma
    _ = (∑ e ∈ edges, 4 * L * flow e / sigma) + edges.card := by
      rw [Finset.sum_add_distrib]
      simp
    _ = (4 * L / sigma) * (∑ e ∈ edges, flow e) + edges.card := by
      apply congrArg (fun z : ℝ ↦ z + (edges.card : ℝ))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      ring









/-- Per-label request count bounded by normalized incident mass plus the
literal support degree. -/
theorem cast_tangentIncidentRequestCount_le
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ e ∈ edges, 0 ≤ flow e)
    (hL : 0 < L) (hsigma : 0 < sigma) (p : P) :
    (tangentIncidentRequestCount edges source target L sigma flow p : ℝ) ≤
      (4 * L / sigma) *
          tangentIncidentFlowMass edges source target flow p +
        tangentSupportDegree edges source target p := by
  unfold tangentIncidentRequestCount tangentIncidentFlowMass
    tangentSupportDegree
  apply cast_tangentRequestTotal_le
  · intro e he
    exact hflow e (Finset.mem_filter.mp he).1
  · exact hL
  · exact hsigma

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCollisionLocalLemma -/
section


/-!
# The finite collision experiment for tangent requests

This file instantiates the finite asymmetric local lemma with the literal
random experiment used in Section 9.  Every request independently chooses a
uniform element of its own nonempty finite multiplier list.  Bad events are
indexed by two-element sets of requests and say that the two resulting
two-element endpoint sets intersect.  Two bad events are declared dependent
exactly when their request supports intersect.

The paper-facing input is the per-request collision estimate

`sum_{E containing r} P(E) <= 1 / 8`.

It implies, inside this file, both `P(E) <= 1 / 8` and the factor-two
neighborhood estimate `sum_{F in Gamma(E)} P(F) <= 1 / 4`.  Thus the literal
choice `x_E = 2 * P(E)` satisfies the numerical local-lemma inequality via
`TangentLLLNumerics`.  Independence is not assumed: it is derived from the
finite product measure and disjoint coordinate supports.

The last theorem specializes the construction to the actual clean common
lists already defined in `TangentCommonMultiplierLists`.  The two remaining
paper inputs are deliberately visible there: nonemptiness of every clean list
and the `1 / 8` collision-mass estimate.  Those are the analytic common-list
cardinality and collision-count estimates, not another local-lemma premise.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos390.WholePaper

noncomputable section

/-! ## The finite product experiment -/







theorem tangentUniformMultiplierMeasure_isProbability
    {Request : Type*} [Fintype Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty) :
    IsProbabilityMeasure (tangentUniformMultiplierMeasure lists hlist) := by
  unfold tangentUniformMultiplierMeasure
  infer_instance

/-- The coordinate choices in the preceding product experiment are mutually
independent. -/
theorem tangentUniformMultiplierCoordinates_iIndep
    {Request : Type*} [Fintype Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty) :
    iIndepFun
      (fun request (outcome : TangentMultiplierOutcome lists) ↦
        outcome request)
      (tangentUniformMultiplierMeasure lists hlist) := by
  unfold tangentUniformMultiplierMeasure
  letI : ∀ request, Nonempty (TangentMultiplierChoice lists request) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request)
  exact iIndepFun_pi fun _request ↦ measurable_id.aemeasurable

/-! ## Collision events and their supports -/

























theorem avoidTangentCollisionEvents_eq_preimage
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collisions : Finset (TangentCollisionIndex Request)) :
    avoidEvents (tangentCollisionEvent (lists := lists) source target)
        collisions =
      (fun outcome
          (request : ↑(tangentCollisionSupportUnion collisions)) ↦
        outcome request.1) ⁻¹'
          tangentAvoidCollisionConfigurations
            (lists := lists) source target collisions := by
  ext outcome
  simp only [avoidEvents, Set.mem_iInter, Set.mem_compl_iff,
    Set.mem_preimage, tangentAvoidCollisionConfigurations]
  constructor
  · intro havoid collision hcollision
    have h := havoid collision hcollision
    simpa only [tangentCollisionEvent, tangentRestrictMultiplierOutcome]
      using h
  · intro havoid collision hcollision
    have h := havoid collision hcollision
    simpa only [tangentCollisionEvent, tangentRestrictMultiplierOutcome]
      using h

/-! ## Product-space dependency factorization -/

/-- Events on a two-request support are independent of simultaneous
avoidance of any finite family of events whose union support is disjoint from
that pair.  The support disjointness is derived from the declared dependency
graph; the measure factorization itself comes from `iIndepFun_pi`. -/
theorem tangentCollisionEvent_independent_of_nonNeighbors
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (collisions : Finset (TangentCollisionIndex Request))
    (hcollision : collision ∉ collisions)
    (hdisjoint : Disjoint collisions
      (tangentCollisionNeighbors collision)) :
    let μ := tangentUniformMultiplierMeasure lists hlist
    μ.real (tangentCollisionEvent source target collision ∩
        avoidEvents (tangentCollisionEvent source target) collisions) =
      μ.real (tangentCollisionEvent source target collision) *
        μ.real (avoidEvents
          (tangentCollisionEvent source target) collisions) := by
  let μ := tangentUniformMultiplierMeasure lists hlist
  let unionSupport := tangentCollisionSupportUnion collisions
  let leftRestriction :=
    fun (outcome : TangentMultiplierOutcome lists)
        (request : ↑collision.1) ↦ outcome request.1
  let rightRestriction :=
    fun (outcome : TangentMultiplierOutcome lists)
        (request : ↑unionSupport) ↦ outcome request.1
  have hsupportDisjoint : Disjoint collision.1 unionSupport := by
    rw [Finset.disjoint_left]
    intro request hrequestCollision hrequestUnion
    obtain ⟨other, hother, hrequestOther⟩ :=
      Finset.mem_biUnion.mp hrequestUnion
    have hotherNe : other ≠ collision := by
      intro heq
      subst other
      exact hcollision hother
    have hoverlap : ¬Disjoint collision.1 other.1 :=
      Finset.not_disjoint_iff.mpr
        ⟨request, hrequestCollision, hrequestOther⟩
    have hotherNeighbor : other ∈ tangentCollisionNeighbors collision := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ other, hotherNe, hoverlap⟩
    exact Finset.disjoint_left.mp hdisjoint hother hotherNeighbor
  have hcoordinateMeasurable :
      ∀ request,
        Measurable (fun outcome : TangentMultiplierOutcome lists ↦
          outcome request) :=
    fun request ↦ measurable_pi_apply request
  have hindepFun : IndepFun leftRestriction rightRestriction μ := by
    dsimp only [leftRestriction, rightRestriction, unionSupport, μ]
    exact (tangentUniformMultiplierCoordinates_iIndep lists hlist).indepFun_finset
      collision.1 (tangentCollisionSupportUnion collisions)
      hsupportDisjoint hcoordinateMeasurable
  have hleftMeasurable : Measurable leftRestriction := by
    dsimp only [leftRestriction]
    exact measurable_pi_iff.mpr fun request ↦
      measurable_pi_apply request.1
  have hrightMeasurable : Measurable rightRestriction := by
    dsimp only [rightRestriction, unionSupport]
    exact measurable_pi_iff.mpr fun request ↦
      measurable_pi_apply request.1
  let collisionConfigurations :
      Set (∀ request : ↑collision.1,
        TangentMultiplierChoice lists request.1) :=
    {restricted | tangentCollisionOn source target collision restricted}
  let safeConfigurations :
      Set (∀ request : ↑unionSupport,
        TangentMultiplierChoice lists request.1) :=
    tangentAvoidCollisionConfigurations source target collisions
  letI : IsProbabilityMeasure μ :=
    tangentUniformMultiplierMeasure_isProbability lists hlist
  have hindepSet : IndepSet
      (leftRestriction ⁻¹' collisionConfigurations)
      (rightRestriction ⁻¹' safeConfigurations) μ :=
    ((indepFun_iff_indepSet_preimage hleftMeasurable hrightMeasurable).mp
      hindepFun) collisionConfigurations safeConfigurations
        (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
  have hmeasure := hindepSet.measure_inter_eq_mul
  have hevent :
      tangentCollisionEvent source target collision =
        leftRestriction ⁻¹' collisionConfigurations := by
    rfl
  have havoid :
      avoidEvents (tangentCollisionEvent source target) collisions =
        rightRestriction ⁻¹' safeConfigurations := by
    dsimp only [rightRestriction, safeConfigurations, unionSupport]
    exact avoidTangentCollisionEvents_eq_preimage source target collisions
  rw [← hevent, ← havoid] at hmeasure
  simpa only [Measure.real, ENNReal.toReal_mul] using
    congrArg ENNReal.toReal hmeasure

/-! ## The literal `1/8`, factor-two, and factor-four bookkeeping -/





private theorem sum_union_le_add_sum_of_nonneg
    {α : Type*} [DecidableEq α]
    (s t : Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s ∪ t, f a ≤ (∑ a ∈ s, f a) + ∑ a ∈ t, f a := by
  calc
    (∑ a ∈ s ∪ t, f a) =
        ∑ a ∈ s ∪ (t \ s), f a := by
          rw [Finset.union_sdiff_self_eq_union]
    _ = (∑ a ∈ s, f a) + ∑ a ∈ t \ s, f a := by
      rw [Finset.sum_union Finset.disjoint_sdiff]
    _ ≤ (∑ a ∈ s, f a) + ∑ a ∈ t, f a := by
      exact add_le_add (le_refl _)
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun a _ha _hnew ↦ hf a))

private theorem sum_biUnion_le_sum_sum_of_nonneg
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤
      ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (sum_union_le_add_sum_of_nonneg
        (t i) (s.biUnion t) f hf).trans
          (add_le_add (le_refl _) ih)

/-- A two-request event is itself bounded by either one of its incident
request masses, hence by the paper's literal `1/8`. -/
theorem tangentCollisionProbability_le_eighth_of_requestMass
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass lists hlist source target request ≤ 1 / 8)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionProbability lists hlist source target collision ≤ 1 / 8 := by
  have hnonempty : collision.1.Nonempty := by
    rw [← Finset.card_pos, collision.2]
    norm_num
  obtain ⟨request, hrequest⟩ := hnonempty
  have hincident : collision ∈ tangentIncidentCollisions request := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ collision, hrequest⟩
  calc
    tangentCollisionProbability lists hlist source target collision ≤
        ∑ event ∈ tangentIncidentCollisions request,
          tangentCollisionProbability lists hlist source target event := by
      exact Finset.single_le_sum
        (fun event _hevent ↦ measureReal_nonneg) hincident
    _ = tangentRequestCollisionMass lists hlist source target request := rfl
    _ ≤ 1 / 8 := hrequestMass request

/-- The dependency neighborhood of a two-request event is covered by the
incident collision families of its two requests.  Summing the two `1/8`
bounds gives the literal factor-two estimate `1/4`. -/
theorem tangentCollisionNeighborhoodMass_le_quarter_of_requestMass
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass lists hlist source target request ≤ 1 / 8)
    (collision : TangentCollisionIndex Request) :
    ∑ other ∈ tangentCollisionNeighbors collision,
        tangentCollisionProbability lists hlist source target other ≤
      1 / 4 := by
  let probability :=
    tangentCollisionProbability lists hlist source target
  have hprobabilityNonneg : ∀ event, 0 ≤ probability event :=
    fun _event ↦ measureReal_nonneg
  have hneighborSubset : tangentCollisionNeighbors collision ⊆
      collision.1.biUnion tangentIncidentCollisions := by
    intro other hother
    have hotherData := Finset.mem_filter.mp hother
    obtain ⟨request, hrequestCollision, hrequestOther⟩ :=
      Finset.not_disjoint_iff.mp hotherData.2.2
    exact Finset.mem_biUnion.mpr
      ⟨request, hrequestCollision, Finset.mem_filter.mpr
        ⟨Finset.mem_univ other, hrequestOther⟩⟩
  calc
    (∑ other ∈ tangentCollisionNeighbors collision, probability other) ≤
        ∑ other ∈ collision.1.biUnion tangentIncidentCollisions,
          probability other := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hneighborSubset
        (fun event _hevent _hnew ↦ hprobabilityNonneg event)
    _ ≤ ∑ request ∈ collision.1,
        ∑ other ∈ tangentIncidentCollisions request,
          probability other :=
      sum_biUnion_le_sum_sum_of_nonneg collision.1
        tangentIncidentCollisions probability hprobabilityNonneg
    _ = ∑ request ∈ collision.1,
        tangentRequestCollisionMass lists hlist source target request := rfl
    _ ≤ ∑ _request ∈ collision.1, (1 / 8 : ℝ) := by
      exact Finset.sum_le_sum fun request _hrequest ↦ hrequestMass request
    _ = 1 / 4 := by
      norm_num [collision.2, Finset.sum_const]

/-- With `x_E = 2 P(E)`, the `1/8` request-mass estimate gives the complete
asymmetric-LLL numerical inequality.  This is the factor-four line of the
paper: the doubled mass in a dependency neighborhood is at most `1/2`. -/
theorem tangentCollisionLLLNumerics_of_requestMass
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass lists hlist source target request ≤ 1 / 8)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionProbability lists hlist source target collision ≤
      (2 * tangentCollisionProbability lists hlist source target collision) *
        ∏ other ∈ tangentCollisionNeighbors collision,
          (1 - 2 *
            tangentCollisionProbability lists hlist source target other) := by
  exact probability_le_two_mul_probability_mul_neighborProduct_of_requestMass
    (tangentCollisionNeighbors collision)
    (tangentCollisionProbability lists hlist source target) collision
    (fun _event _hevent ↦ measureReal_nonneg) (1 / 8 : ℝ) (by norm_num)
    (by
      have hquarter :=
        tangentCollisionNeighborhoodMass_le_quarter_of_requestMass
          lists hlist source target hrequestMass collision
      nlinarith)

/-! ## The collision-free outcome -/

/-- Finite product-space specialization of the local lemma used in Section
9.  It constructs an outcome avoiding every collision event; neither
collision-free existence nor the local-lemma conclusion is an input. -/
theorem tangentCollisionFreeOutcome_of_requestMass
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass lists hlist source target request ≤ 1 / 8) :
    ∃ outcome : TangentMultiplierOutcome lists,
      ∀ collision : TangentCollisionIndex Request,
        outcome ∉ tangentCollisionEvent source target collision := by
  let μ := tangentUniformMultiplierMeasure lists hlist
  let event := tangentCollisionEvent (lists := lists) source target
  let probability :=
    tangentCollisionProbability lists hlist source target
  let x := fun collision : TangentCollisionIndex Request ↦
    2 * probability collision
  letI : IsProbabilityMeasure μ :=
    tangentUniformMultiplierMeasure_isProbability lists hlist
  apply finiteAsymmetricLocalLemma μ event tangentCollisionNeighbors x
  · intro collision
    exact (Set.toFinite (event collision)).measurableSet
  · intro collision
    have heventBound :=
      tangentCollisionProbability_le_eighth_of_requestMass
        lists hlist source target hrequestMass collision
    constructor
    · dsimp only [x, probability]
      exact mul_nonneg (by norm_num) measureReal_nonneg
    · dsimp only [x, probability]
      linarith
  · intro collision collisions hcollision hdisjoint
    dsimp only [μ, event]
    exact tangentCollisionEvent_independent_of_nonNeighbors
      lists hlist source target collision collisions
        hcollision hdisjoint
  · intro collision
    dsimp only [μ, event, x, probability]
    exact tangentCollisionLLLNumerics_of_requestMass
      lists hlist source target hrequestMass collision

/-- Avoidance of all two-request collision events gives the deterministic
endpoint-distinctness structure consumed by the tangent feasibility layer.
The only extra facts needed are that the two labels of one request differ
and that its selected multiplier is nonzero. -/
theorem tangentEndpointsDistinct_of_avoidsCollisions
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (outcome : TangentMultiplierOutcome lists)
    (hsourceTarget : ∀ request, source request ≠ target request)
    (hmultiplier : ∀ request, (outcome request).1 ≠ 0)
    (havoid : ∀ collision : TangentCollisionIndex Request,
      outcome ∉ tangentCollisionEvent source target collision) :
    TangentEndpointsDistinct Finset.univ source target
      (fun request ↦ (outcome request).1) := by
  have hpairwise : ∀ r s : Request, r ≠ s →
      Disjoint
        (tangentRequestEndpointSet source target
          (fun request ↦ (outcome request).1) r)
        (tangentRequestEndpointSet source target
          (fun request ↦ (outcome request).1) s) := by
    intro r s hrs
    by_contra hoverlap
    let collision : TangentCollisionIndex Request :=
      ⟨{r, s}, by simp [hrs]⟩
    have hr : r ∈ collision.1 := by simp [collision]
    have hs : s ∈ collision.1 := by simp [collision]
    apply havoid collision
    change tangentCollisionOn source target collision
      (fun request ↦ outcome request.1)
    refine ⟨⟨r, hr⟩, ⟨s, hs⟩, ?_, ?_⟩
    · intro heq
      exact hrs (congrArg Subtype.val heq)
    · simpa only [tangentRestrictedEndpointSet,
        tangentRequestEndpointSet] using hoverlap
  refine ⟨?_, ?_, ?_⟩
  · intro r _hr s _hs heq
    by_contra hrs
    change source r * (outcome r).1 =
      source s * (outcome s).1 at heq
    have hdisjoint := hpairwise r s hrs
    have hleft : source r * (outcome r).1 ∈
        tangentRequestEndpointSet source target
          (fun request ↦ (outcome request).1) r := by
      simp [tangentRequestEndpointSet]
    have hright : source r * (outcome r).1 ∈
        tangentRequestEndpointSet source target
          (fun request ↦ (outcome request).1) s := by
      simp [tangentRequestEndpointSet, heq]
    exact Finset.disjoint_left.mp hdisjoint hleft hright
  · intro r _hr s _hs heq
    by_contra hrs
    change target r * (outcome r).1 =
      target s * (outcome s).1 at heq
    have hdisjoint := hpairwise r s hrs
    have hleft : target r * (outcome r).1 ∈
        tangentRequestEndpointSet source target
          (fun request ↦ (outcome request).1) r := by
      simp [tangentRequestEndpointSet]
    have hright : target r * (outcome r).1 ∈
        tangentRequestEndpointSet source target
          (fun request ↦ (outcome request).1) s := by
      simp [tangentRequestEndpointSet, heq]
    exact Finset.disjoint_left.mp hdisjoint hleft hright
  · intro r _hr s _hs
    by_cases hrs : r = s
    · subst s
      intro heq
      exact hsourceTarget r (mul_right_cancel₀ (hmultiplier r) heq)
    · intro heq
      have hdisjoint := hpairwise r s hrs
      have hleft : source r * (outcome r).1 ∈
          tangentRequestEndpointSet source target
            (fun request ↦ (outcome request).1) r := by
        simp [tangentRequestEndpointSet]
      have hright : source r * (outcome r).1 ∈
          tangentRequestEndpointSet source target
            (fun request ↦ (outcome request).1) s := by
        rw [heq]
        simp [tangentRequestEndpointSet]
      exact Finset.disjoint_left.mp hdisjoint hleft hright

/-- Paper-facing deterministic output of the finite collision experiment. -/
theorem tangentEndpointsDistinct_of_requestMass
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (hsourceTarget : ∀ request, source request ≠ target request)
    (hpositive : ∀ request, ∀ multiplier ∈ lists request,
      multiplier ≠ 0)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass lists hlist source target request ≤ 1 / 8) :
    ∃ outcome : TangentMultiplierOutcome lists,
      TangentEndpointsDistinct Finset.univ source target
        (fun request ↦ (outcome request).1) := by
  obtain ⟨outcome, havoid⟩ := tangentCollisionFreeOutcome_of_requestMass
    lists hlist source target hrequestMass
  exact ⟨outcome,
    tangentEndpointsDistinct_of_avoidsCollisions source target outcome
      hsourceTarget (fun request ↦
        hpositive request (outcome request).1 (outcome request).2) havoid⟩

/-! ## Specialization to the literal clean common lists -/



/-- Applying the finite collision experiment to the literal clean lists
produces actual numerical multipliers, proves their list membership, and
supplies `TangentEndpointsDistinct`.  The visible hypotheses are exactly the
two estimates not yet proved by the current common-list API: list
nonemptiness and per-request collision mass at most `1/8`. -/
theorem tangentCleanCommonMultiplier_collisionFree_of_requestMass
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ request, source request ≠ target request)
    (hlist : ∀ request,
      (tangentCleanMultiplierLists n K h Phead X0 y source target
        dedicatedRows numericalGuards request).Nonempty)
    (hrequestMass : ∀ request,
      tangentRequestCollisionMass
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards)
        hlist source target request ≤ 1 / 8) :
    ∃ multiplier : Request → ℕ,
      (∀ request,
        multiplier request ∈
          tangentCleanCommonMultiplierList
            n K h Phead X0 y
              (max (source request) (target request))
              (min (source request) (target request))
              dedicatedRows numericalGuards) ∧
      TangentEndpointsDistinct Finset.univ source target multiplier := by
  let lists := tangentCleanMultiplierLists
    n K h Phead X0 y source target dedicatedRows numericalGuards
  obtain ⟨outcome, hdistinct⟩ := tangentEndpointsDistinct_of_requestMass
    lists hlist source target hsourceTarget
    (by
      intro request multiplier hmultiplier
      change multiplier ∈ tangentCleanCommonMultiplierList
        n K h Phead X0 y
          (max (source request) (target request))
          (min (source request) (target request))
          dedicatedRows numericalGuards at hmultiplier
      have hbounds := mem_tangentCleanCommonMultiplierList.mp hmultiplier
      exact (lt_of_le_of_lt (Nat.zero_le _) hbounds.1.1).ne')
    hrequestMass
  refine ⟨fun request ↦ (outcome request).1, ?_, hdistinct⟩
  intro request
  simpa only [lists, tangentCleanMultiplierLists] using
    (outcome request).2

/-! ## The literal split-request specialization -/



/-- Direct bridge from the actual split-request family to the endpoint
certificate consumed by `tangentSplitUpdate_feasible_and_margin`. -/
theorem tangentSplitEndpointsDistinct_of_cleanRequestMass
    {E : Type*} [DecidableEq E] (edges : Finset E)
    (source target : E → ℕ) (L sigma : ℝ) (flow : E → ℝ)
    (n K h Phead X0 y : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentSplitRequestSource source request ≠
        tangentSplitRequestTarget target request)
    (hlist : ∀ request : TangentSplitRequest edges L sigma flow,
      (tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request).Nonempty)
    (hrequestMass : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentRequestCollisionMass
        (tangentSplitCleanMultiplierLists edges source target L sigma flow
          n K h Phead X0 y dedicatedRows numericalGuards)
        hlist (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists edges source target L sigma flow
            n K h Phead X0 y dedicatedRows numericalGuards request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) multiplier := by
  obtain ⟨multiplier, hmem, hdistinct⟩ :=
    tangentCleanCommonMultiplier_collisionFree_of_requestMass
      n K h Phead X0 y
      (tangentSplitRequestSource source)
      (tangentSplitRequestTarget target)
      dedicatedRows numericalGuards hsourceTarget hlist hrequestMass
  refine ⟨multiplier, ?_, ?_⟩
  · intro request
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists] using hmem request
  · simpa only [tangentSplitRequests] using hdistinct

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCollisionCounting -/
section


/-!
# Counting the tangent collision events

This file is the finite counting layer immediately before the local-lemma
module.  It does three things which are kept separate in the paper's prose.

* It proves that the product of the request-wise uniform laws is the uniform
  law on the finite dependent product.  Consequently an actual collision
  probability is exactly

  `number of colliding configurations / number of all configurations`.

* A two-request collision is covered by the four literal endpoint equations.
  For prime endpoint labels, the equation `p*a=q*b` has at most
  `N/p+1` solutions when `p=q`, and at most `N/(p*q)+1` solutions when
  `p != q`, provided the left endpoint is at most `N`.

* The incident-event sum for one request is reindexed exactly by all other
  requests.  A pairwise cardinality/counting estimate can therefore be
  summed using the two endpoint-label loads of the fixed request and the
  total request count.

No collision-free choice and no bound on a collision probability are assumed
here.  In the clean-list terminal the remaining inputs are request-wise list
cardinality lower bounds and an explicit arithmetic comparison of the finite
counting budget with the paper's shared-label and disjoint-label charges.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos390.WholePaper

noncomputable section

/-! ## The product law is uniform -/



/-- Cardinality formula for the preceding abstract finite uniform law. -/
theorem tangentFiniteUniformMeasure_apply
    (α : Type*) [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] (hα : Nonempty α)
    (s : Set α) (hs : MeasurableSet s) :
    tangentFiniteUniformMeasure α hα s = Nat.card s / Nat.card α := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Nonempty α := hα
  unfold tangentFiniteUniformMeasure
  calc
    (PMF.uniformOfFintype α).toMeasure s =
        Fintype.card s / Fintype.card α :=
      PMF.toMeasure_uniformOfFintype_apply s hs
    _ = Nat.card s / Nat.card α := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]





/-- A finite product of nonempty uniform list laws is the uniform law on the
dependent product of the list subtypes. -/
theorem tangentUniformMultiplierMeasure_eq_uniformOfFintype
    {Request : Type*} [Fintype Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty) :
    tangentUniformMultiplierMeasure lists hlist =
      tangentUniformMultiplierOutcomeMeasure lists hlist := by
  classical
  letI : ∀ request, Nonempty (TangentMultiplierChoice lists request) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request)
  apply Measure.ext_of_singleton
  intro outcome
  unfold tangentUniformMultiplierMeasure
    tangentUniformMultiplierOutcomeMeasure tangentFiniteUniformMeasure
  rw [Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _)]
  simp_rw [PMF.uniformOfFintype_apply]
  simp_rw [Fintype.card_eq_nat_card]
  rw [Nat.card_pi]
  simp_rw [Nat.card_eq_finsetCard, Nat.cast_prod]
  rw [ENNReal.prod_inv_distrib]
  exact fun _ _ _ _ _ ↦ Or.inr ENNReal.coe_ne_top

/-- Restricting the full product experiment to any finite set of request
coordinates gives the uniform law on the corresponding dependent product. -/
theorem tangentUniformMultiplierRestriction_map_eq_uniformOfFintype
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (support : Finset Request) :
    (tangentUniformMultiplierMeasure lists hlist).map
        (fun outcome (request : ↑support) ↦ outcome request.1) =
      tangentUniformMultiplierRestrictionMeasure lists hlist support := by
  let μ := tangentUniformMultiplierMeasure lists hlist
  let restrictedLists : ↑support → Finset ℕ :=
    fun request ↦ lists request.1
  let hrestricted : ∀ request, (restrictedLists request).Nonempty :=
    fun request ↦ hlist request.1
  letI : ∀ request, Nonempty (TangentMultiplierChoice lists request) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request)
  letI : IsProbabilityMeasure μ :=
    tangentUniformMultiplierMeasure_isProbability lists hlist
  have hindep : iIndepFun
      (fun request : ↑support =>
        fun outcome : TangentMultiplierOutcome lists => outcome request.1) μ :=
    (tangentUniformMultiplierCoordinates_iIndep lists hlist).precomp
      Subtype.val_injective
  have hcoordinate : ∀ request : ↑support,
      μ.map (fun outcome : TangentMultiplierOutcome lists ↦ outcome request.1) =
        (PMF.uniformOfFintype
          (TangentMultiplierChoice lists request.1)).toMeasure := by
    intro request
    dsimp only [μ]
    unfold tangentUniformMultiplierMeasure
    letI : ∀ r, Nonempty (TangentMultiplierChoice lists r) :=
      fun r ↦ Finset.nonempty_coe_sort.mpr (hlist r)
    exact (measurePreserving_eval
      (fun r ↦ (PMF.uniformOfFintype
        (TangentMultiplierChoice lists r)).toMeasure) request.1).map_eq
  calc
    μ.map (fun outcome (request : ↑support) ↦ outcome request.1) =
        Measure.pi (fun request : ↑support ↦
          μ.map (fun outcome : TangentMultiplierOutcome lists ↦
            outcome request.1)) :=
      (iIndepFun_iff_map_fun_eq_pi_map
        (fun request : ↑support ↦
          (measurable_pi_apply request.1).aemeasurable)).mp hindep
    _ = tangentUniformMultiplierMeasure restrictedLists hrestricted := by
      change Measure.pi (fun request : ↑support ↦
          μ.map (fun outcome : TangentMultiplierOutcome lists ↦
            outcome request.1)) =
        Measure.pi (fun request : ↑support ↦
          (PMF.uniformOfFintype
            (TangentMultiplierChoice lists request.1)).toMeasure)
      have hmeasureFamily :
          (fun request : ↑support ↦
            μ.map (fun outcome : TangentMultiplierOutcome lists ↦
              outcome request.1)) =
          (fun request : ↑support ↦
            (PMF.uniformOfFintype
              (TangentMultiplierChoice lists request.1)).toMeasure) :=
        funext hcoordinate
      exact congrArg (fun measures ↦ Measure.pi measures) hmeasureFamily
    _ = tangentUniformMultiplierRestrictionMeasure lists hlist support := by
      simpa only [tangentUniformMultiplierRestrictionMeasure,
        restrictedLists, hrestricted] using
        tangentUniformMultiplierMeasure_eq_uniformOfFintype
          (Request := ↑support) restrictedLists hrestricted

/-- Cardinality formula for the preceding supported uniform measure. -/
theorem tangentUniformMultiplierRestrictionMeasure_apply
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (support : Finset Request)
    (s : Set (∀ request : ↑support,
      TangentMultiplierChoice lists request.1))
    (hs : MeasurableSet s) :
    tangentUniformMultiplierRestrictionMeasure lists hlist support s =
      Nat.card s /
        Nat.card (∀ request : ↑support,
          TangentMultiplierChoice lists request.1) := by
  classical
  letI : ∀ request : ↑support,
      Nonempty (TangentMultiplierChoice lists request.1) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request.1)
  unfold tangentUniformMultiplierRestrictionMeasure
    tangentUniformMultiplierOutcomeMeasure
  exact tangentFiniteUniformMeasure_apply
    (∀ request : ↑support,
      TangentMultiplierChoice lists request.1) inferInstance s hs

/-! ## Exact collision configurations -/







/-- The actual collision probability is exactly the ratio of the number of
colliding configurations to the product of the two list cardinalities. -/
theorem tangentCollisionProbability_eq_configurationCount_div
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionProbability lists hlist source target collision =
      ((tangentCollisionConfigurations
          (lists := lists) source target collision).card : ℝ) /
        tangentCollisionChoiceCount (lists := lists) collision := by
  classical
  let restriction := fun outcome : TangentMultiplierOutcome lists =>
    fun request : ↑collision.1 => outcome request.1
  have hrestriction : Measurable restriction := by
    exact measurable_pi_iff.mpr fun request ↦ measurable_pi_apply request.1
  have hcollisionMeasurable : MeasurableSet
      ({outcome : TangentCollisionConfiguration (lists := lists) collision |
        tangentCollisionOn source target collision outcome} : Set _) :=
    (Set.toFinite _).measurableSet
  rw [tangentCollisionProbability]
  change ENNReal.toReal
      ((tangentUniformMultiplierMeasure lists hlist)
        (restriction ⁻¹'
          {outcome | tangentCollisionOn source target collision outcome})) = _
  rw [← Measure.map_apply hrestriction hcollisionMeasurable,
    tangentUniformMultiplierRestriction_map_eq_uniformOfFintype
      lists hlist collision.1]
  rw [tangentUniformMultiplierRestrictionMeasure_apply
    lists hlist collision.1
      {outcome | tangentCollisionOn source target collision outcome}
      hcollisionMeasurable]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_coe,
    tangentCollisionChoiceCount]
  congr 1
  rw [Fintype.card_subtype]
  rfl

/-! ## Naming the two requests and the four endpoint equations -/





theorem tangentCollisionFirstRequest_ne_secondRequest
    {Request : Type*} (collision : TangentCollisionIndex Request) :
    tangentCollisionFirstRequest collision ≠
      tangentCollisionSecondRequest collision := by
  intro heq
  have h := congrArg (collision.1.equivFinOfCardEq collision.2) heq
  have hzeroOne : (0 : Fin 2) = 1 := by
    simpa only [tangentCollisionFirstRequest,
      tangentCollisionSecondRequest, Equiv.apply_symm_apply] using h
  exact Fin.zero_ne_one hzeroOne

/-- The canonical two requests exhaust the support. -/
theorem tangentCollisionSupport_eq_pair
    {Request : Type*} [DecidableEq Request]
    (collision : TangentCollisionIndex Request) :
    collision.1 =
      {(tangentCollisionFirstRequest collision).1,
        (tangentCollisionSecondRequest collision).1} := by
  let first := tangentCollisionFirstRequest collision
  let second := tangentCollisionSecondRequest collision
  have hne : first.1 ≠ second.1 := by
    intro h
    exact tangentCollisionFirstRequest_ne_secondRequest collision
      (Subtype.ext h)
  have hsubset : ({first.1, second.1} : Finset Request) ⊆ collision.1 := by
    intro request hrequest
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrequest
    rcases hrequest with rfl | rfl
    · exact first.2
    · exact second.2
  have hcard : collision.1.card ≤
      ({first.1, second.1} : Finset Request).card := by
    rw [collision.2, Finset.card_pair hne]
  exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

/-- The existential collision predicate can be read using the canonical
first and second requests. -/
theorem tangentCollisionOn_iff_canonicalPair
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (outcome : TangentCollisionConfiguration
      (lists := lists) collision) :
    tangentCollisionOn source target collision outcome ↔
      ¬Disjoint
        (tangentRestrictedEndpointSet source target collision.1 outcome
          (tangentCollisionFirstRequest collision))
        (tangentRestrictedEndpointSet source target collision.1 outcome
          (tangentCollisionSecondRequest collision)) := by
  let first := tangentCollisionFirstRequest collision
  let second := tangentCollisionSecondRequest collision
  have hsupport : collision.1 =
      ({first.1, second.1} : Finset Request) :=
    tangentCollisionSupport_eq_pair collision
  have hsupportSubset : collision.1 ⊆
      ({first.1, second.1} : Finset Request) := by
    intro request hrequest
    rw [← hsupport]
    exact hrequest
  constructor
  · rintro ⟨r, s, hrs, hoverlap⟩
    have hr : r.1 = first.1 ∨ r.1 = second.1 := by
      have hmem := hsupportSubset r.property
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    have hs : s.1 = first.1 ∨ s.1 = second.1 := by
      have hmem := hsupportSubset s.property
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · exact (hrs (Subtype.ext (hr.trans hs.symm))).elim
    · have hrEq : r = first := Subtype.ext hr
      have hsEq : s = second := Subtype.ext hs
      subst r
      subst s
      exact hoverlap
    · have hrEq : r = second := Subtype.ext hr
      have hsEq : s = first := Subtype.ext hs
      subst r
      subst s
      simpa only [_root_.disjoint_comm] using hoverlap
    · exact (hrs (Subtype.ext (hr.trans hs.symm))).elim
  · intro hoverlap
    exact ⟨first, second,
      tangentCollisionFirstRequest_ne_secondRequest collision,
      by simpa only [first, second] using hoverlap⟩







/-- Collision is equivalent to one of the literal four endpoint equations. -/
theorem tangentCollisionOn_iff_exists_endpointEquation
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (outcome : TangentCollisionConfiguration
      (lists := lists) collision) :
    tangentCollisionOn source target collision outcome ↔
      ∃ leftSide rightSide : TangentEndpointSide,
        tangentRestrictedEndpointValue source target outcome leftSide
            (tangentCollisionFirstRequest collision) =
          tangentRestrictedEndpointValue source target outcome rightSide
            (tangentCollisionSecondRequest collision) := by
  rw [tangentCollisionOn_iff_canonicalPair]
  constructor
  · intro hoverlap
    obtain ⟨value, hleft, hright⟩ :=
      Finset.not_disjoint_iff.mp hoverlap
    simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
      Finset.mem_singleton] at hleft hright
    rcases hleft with hleft | hleft <;>
      rcases hright with hright | hright
    · exact ⟨.source, .source, by
        simpa [tangentRestrictedEndpointValue, tangentEndpointLabel]
          using hleft.symm.trans hright⟩
    · exact ⟨.source, .target, by
        simpa [tangentRestrictedEndpointValue, tangentEndpointLabel]
          using hleft.symm.trans hright⟩
    · exact ⟨.target, .source, by
        simpa [tangentRestrictedEndpointValue, tangentEndpointLabel]
          using hleft.symm.trans hright⟩
    · exact ⟨.target, .target, by
        simpa [tangentRestrictedEndpointValue, tangentEndpointLabel]
          using hleft.symm.trans hright⟩
  · rintro ⟨leftSide, rightSide, heq⟩
    apply Finset.not_disjoint_iff.mpr
    cases leftSide <;> cases rightSide
    all_goals
      simp only [tangentRestrictedEndpointValue,
        tangentEndpointLabel] at heq
    · exact ⟨source (tangentCollisionFirstRequest collision).1 *
          (outcome (tangentCollisionFirstRequest collision)).1,
        by
          simp [tangentRestrictedEndpointSet],
        by
          simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
            Finset.mem_singleton]
          exact Or.inl heq⟩
    · exact ⟨source (tangentCollisionFirstRequest collision).1 *
          (outcome (tangentCollisionFirstRequest collision)).1,
        by
          simp [tangentRestrictedEndpointSet],
        by
          simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
            Finset.mem_singleton]
          exact Or.inr heq⟩
    · exact ⟨target (tangentCollisionFirstRequest collision).1 *
          (outcome (tangentCollisionFirstRequest collision)).1,
        by
          simp [tangentRestrictedEndpointSet],
        by
          simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
            Finset.mem_singleton]
          exact Or.inl heq⟩
    · exact ⟨target (tangentCollisionFirstRequest collision).1 *
          (outcome (tangentCollisionFirstRequest collision)).1,
        by
          simp [tangentRestrictedEndpointSet],
        by
          simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
            Finset.mem_singleton]
          exact Or.inr heq⟩



/-- The collision count is at most the sum of the four endpoint-equation
configuration counts. -/
theorem card_tangentCollisionConfigurations_le_fourEndpointEquations
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) :
    (tangentCollisionConfigurations
      (lists := lists) source target collision).card ≤
      ∑ leftSide : TangentEndpointSide,
        ∑ rightSide : TangentEndpointSide,
          (tangentEndpointEquationConfigurations
            (lists := lists) source target collision
              leftSide rightSide).card := by
  classical
  let equationUnion := Finset.univ.biUnion fun leftSide : TangentEndpointSide ↦
    Finset.univ.biUnion fun rightSide : TangentEndpointSide ↦
      tangentEndpointEquationConfigurations
        (lists := lists) source target collision leftSide rightSide
  have hsubset : tangentCollisionConfigurations
    (lists := lists) source target collision ⊆ equationUnion := by
    intro outcome houtcome
    have hcollision :
        tangentCollisionOn source target collision outcome := by
      simpa only [tangentCollisionConfigurations, Finset.mem_filter,
        Finset.mem_univ, true_and] using houtcome
    obtain ⟨leftSide, rightSide, heq⟩ :=
      (tangentCollisionOn_iff_exists_endpointEquation
        source target collision outcome).mp hcollision
    apply Finset.mem_biUnion.mpr
    refine ⟨leftSide, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨rightSide, Finset.mem_univ _, ?_⟩
    simpa only [tangentEndpointEquationConfigurations,
      Finset.mem_filter, Finset.mem_univ, true_and] using heq
  calc
    (tangentCollisionConfigurations
        (lists := lists) source target collision).card ≤
        equationUnion.card := Finset.card_le_card hsubset
    _ ≤ ∑ leftSide ∈ (Finset.univ : Finset TangentEndpointSide),
        (Finset.univ.biUnion fun rightSide : TangentEndpointSide ↦
          tangentEndpointEquationConfigurations
            (lists := lists) source target collision
              leftSide rightSide).card := Finset.card_biUnion_le
    _ ≤ ∑ leftSide ∈ (Finset.univ : Finset TangentEndpointSide),
        ∑ rightSide ∈ (Finset.univ : Finset TangentEndpointSide),
          (tangentEndpointEquationConfigurations
            (lists := lists) source target collision
              leftSide rightSide).card := by
      exact Finset.sum_le_sum fun leftSide _hleft ↦
        Finset.card_biUnion_le
    _ = _ := rfl

/-! ## Raw solutions of `p*a=q*b` -/



/-- Reading the two selected multipliers is injective on assignments to a
two-element support. -/
theorem tangentCollisionValuePair_injective
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (collision : TangentCollisionIndex Request) :
    Function.Injective
      (fun outcome : TangentCollisionConfiguration
          (lists := lists) collision ↦
        ((outcome (tangentCollisionFirstRequest collision)).1,
          (outcome (tangentCollisionSecondRequest collision)).1)) := by
  intro left right heq
  funext request
  apply Subtype.ext
  have hsupport : collision.1 =
      ({(tangentCollisionFirstRequest collision).1,
        (tangentCollisionSecondRequest collision).1} : Finset Request) :=
    tangentCollisionSupport_eq_pair collision
  have hsupportSubset : collision.1 ⊆
      ({(tangentCollisionFirstRequest collision).1,
        (tangentCollisionSecondRequest collision).1} : Finset Request) := by
    intro candidate hcandidate
    rw [← hsupport]
    exact hcandidate
  have hrequest : request.1 =
        (tangentCollisionFirstRequest collision).1 ∨
      request.1 = (tangentCollisionSecondRequest collision).1 := by
    have hmem := hsupportSubset request.property
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hrequest with hrequest | hrequest
  · have hr : request = tangentCollisionFirstRequest collision :=
      Subtype.ext hrequest
    subst request
    exact congrArg Prod.fst heq
  · have hr : request = tangentCollisionSecondRequest collision :=
      Subtype.ext hrequest
    subst request
    exact congrArg Prod.snd heq

/-- An endpoint-equation configuration injects into the raw pair solutions
from the two actual request lists. -/
theorem card_tangentEndpointEquationConfigurations_le_solutions
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (leftSide rightSide : TangentEndpointSide) :
    (tangentEndpointEquationConfigurations
      (lists := lists) source target collision
        leftSide rightSide).card ≤
      (tangentEndpointEquationSolutions
        (lists (tangentCollisionFirstRequest collision).1)
        (lists (tangentCollisionSecondRequest collision).1)
        (tangentEndpointLabel source target leftSide
          (tangentCollisionFirstRequest collision).1)
        (tangentEndpointLabel source target rightSide
          (tangentCollisionSecondRequest collision).1)).card := by
  apply Finset.card_le_card_of_injOn
    (s := tangentEndpointEquationConfigurations
      (lists := lists) source target collision leftSide rightSide)
    (t := tangentEndpointEquationSolutions
      (lists (tangentCollisionFirstRequest collision).1)
      (lists (tangentCollisionSecondRequest collision).1)
      (tangentEndpointLabel source target leftSide
        (tangentCollisionFirstRequest collision).1)
      (tangentEndpointLabel source target rightSide
        (tangentCollisionSecondRequest collision).1))
    (fun outcome ↦
      ((outcome (tangentCollisionFirstRequest collision)).1,
        (outcome (tangentCollisionSecondRequest collision)).1))
  · intro outcome houtcome
    have heq := (Finset.mem_filter.mp houtcome).2
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_product.mpr ⟨
        (outcome (tangentCollisionFirstRequest collision)).2,
        (outcome (tangentCollisionSecondRequest collision)).2⟩,
      by simpa [tangentRestrictedEndpointValue] using heq⟩
  · exact (tangentCollisionValuePair_injective
      (lists := lists) collision).injOn

/-- If the two positive labels are equal, cancellation and the endpoint
cutoff give at most `N/p+1` raw solutions. -/
theorem card_tangentEndpointEquationSolutions_same_le
    {leftList rightList : Finset ℕ} {label N : ℕ}
    (hlabel : 0 < label)
    (hupper : ∀ a ∈ leftList, label * a ≤ N) :
    (tangentEndpointEquationSolutions
      leftList rightList label label).card ≤ N / label + 1 := by
  have hcard : (tangentEndpointEquationSolutions
      leftList rightList label label).card ≤
      (Finset.range (N / label + 1)).card := by
    apply Finset.card_le_card_of_injOn
      (s := tangentEndpointEquationSolutions
        leftList rightList label label)
      (t := Finset.range (N / label + 1))
      (fun pair : ℕ × ℕ ↦ pair.1)
    · intro pair hpair
      have hdata := Finset.mem_filter.mp hpair
      have hleftMem : pair.1 ∈ leftList :=
        (Finset.mem_product.mp hdata.1).1
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_div_iff_mul_le hlabel).mpr
      simpa only [Nat.mul_comm] using hupper pair.1 hleftMem
    · intro left hleft right hright hfirst
      have hleftEq := (Finset.mem_filter.mp hleft).2
      have hrightEq := (Finset.mem_filter.mp hright).2
      change left.1 = right.1 at hfirst
      apply Prod.ext hfirst
      apply mul_left_cancel₀ hlabel.ne'
      calc
        label * left.2 = label * left.1 := hleftEq.symm
        _ = label * right.1 := by rw [hfirst]
        _ = label * right.2 := hrightEq
  simpa only [Finset.card_range] using hcard

/-- For coprime positive distinct labels, write `a=q*m`; the endpoint cutoff
then gives `m <= N/(p*q)`. -/
theorem card_tangentEndpointEquationSolutions_coprime_le
    {leftList rightList : Finset ℕ} {leftLabel rightLabel N : ℕ}
    (hleft : 0 < leftLabel) (hright : 0 < rightLabel)
    (hcoprime : Nat.Coprime leftLabel rightLabel)
    (hupper : ∀ a ∈ leftList, leftLabel * a ≤ N) :
    (tangentEndpointEquationSolutions
      leftList rightList leftLabel rightLabel).card ≤
        N / (leftLabel * rightLabel) + 1 := by
  let quotient := fun pair : ℕ × ℕ ↦ pair.1 / rightLabel
  have hdivisible : ∀ pair ∈
      tangentEndpointEquationSolutions
        leftList rightList leftLabel rightLabel,
      rightLabel ∣ pair.1 := by
    intro pair hpair
    have heq := (Finset.mem_filter.mp hpair).2
    apply (hcoprime.symm.dvd_mul_right).mp
    rw [Nat.mul_comm]
    exact ⟨pair.2, heq⟩
  have hcard : (tangentEndpointEquationSolutions
      leftList rightList leftLabel rightLabel).card ≤
      (Finset.range (N / (leftLabel * rightLabel) + 1)).card := by
    apply Finset.card_le_card_of_injOn
      (s := tangentEndpointEquationSolutions
        leftList rightList leftLabel rightLabel)
      (t := Finset.range (N / (leftLabel * rightLabel) + 1))
      quotient
    · intro pair hpair
      have hproduct : pair ∈ leftList.product rightList :=
        (Finset.mem_filter.mp hpair).1
      have hleftMem : pair.1 ∈ leftList :=
        (Finset.mem_product.mp hproduct).1
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos hleft hright)).mpr
      calc
        quotient pair * (leftLabel * rightLabel) =
            leftLabel * (rightLabel * quotient pair) := by ac_rfl
        _ = leftLabel * pair.1 := by
          rw [Nat.mul_div_cancel' (hdivisible pair hpair)]
        _ ≤ N := hupper pair.1 hleftMem
    · intro left hleftMem right hrightMem hquotient
      have hleftFirst : left.1 = rightLabel * quotient left := by
        exact (Nat.mul_div_cancel' (hdivisible left hleftMem)).symm
      have hrightFirst : right.1 = rightLabel * quotient right := by
        exact (Nat.mul_div_cancel' (hdivisible right hrightMem)).symm
      have hfirst : left.1 = right.1 := by
        rw [hleftFirst, hrightFirst, hquotient]
      apply Prod.ext hfirst
      apply mul_left_cancel₀ hright.ne'
      have hleftEq := (Finset.mem_filter.mp hleftMem).2
      have hrightEq := (Finset.mem_filter.mp hrightMem).2
      calc
        rightLabel * left.2 = leftLabel * left.1 := hleftEq.symm
        _ = leftLabel * right.1 := by rw [hfirst]
        _ = rightLabel * right.2 := hrightEq
  simpa only [Finset.card_range] using hcard



/-- Prime labels obey the preceding literal endpoint-equation budget. -/
theorem card_tangentEndpointEquationSolutions_prime_le_budget
    {leftList rightList : Finset ℕ} {leftLabel rightLabel N : ℕ}
    (hleftPrime : leftLabel.Prime)
    (hrightPrime : rightLabel.Prime)
    (hupper : ∀ a ∈ leftList, leftLabel * a ≤ N) :
    (tangentEndpointEquationSolutions
      leftList rightList leftLabel rightLabel).card ≤
        tangentEndpointEquationBudget N leftLabel rightLabel := by
  by_cases heq : leftLabel = rightLabel
  · subst rightLabel
    simpa [tangentEndpointEquationBudget] using
      card_tangentEndpointEquationSolutions_same_le
        hleftPrime.pos hupper
  · simpa [tangentEndpointEquationBudget, heq] using
      card_tangentEndpointEquationSolutions_coprime_le
        hleftPrime.pos hrightPrime.pos
        ((Nat.coprime_primes hleftPrime hrightPrime).mpr heq) hupper





theorem tangentEndpointEquationBudget_comm
    (N leftLabel rightLabel : ℕ) :
    tangentEndpointEquationBudget N leftLabel rightLabel =
      tangentEndpointEquationBudget N rightLabel leftLabel := by
  by_cases heq : leftLabel = rightLabel
  · subst rightLabel
    rfl
  · have hne : rightLabel ≠ leftLabel := Ne.symm heq
    simp [tangentEndpointEquationBudget, heq, hne, Nat.mul_comm]

theorem tangentOrderedPairEndpointBudget_comm
    {Request : Type*} (N : ℕ) (source target : Request → ℕ)
    (left right : Request) :
    tangentOrderedPairEndpointBudget N source target left right =
      tangentOrderedPairEndpointBudget N source target right left := by
  unfold tangentOrderedPairEndpointBudget
  calc
    (∑ leftSide : TangentEndpointSide,
      ∑ rightSide : TangentEndpointSide,
        tangentEndpointEquationBudget N
          (tangentEndpointLabel source target leftSide left)
          (tangentEndpointLabel source target rightSide right)) =
      ∑ leftSide : TangentEndpointSide,
        ∑ rightSide : TangentEndpointSide,
          tangentEndpointEquationBudget N
            (tangentEndpointLabel source target rightSide right)
            (tangentEndpointLabel source target leftSide left) := by
      exact Finset.sum_congr rfl fun leftSide _hleft ↦
        Finset.sum_congr rfl fun rightSide _hright ↦
          tangentEndpointEquationBudget_comm N _ _
    _ = _ := by rw [Finset.sum_comm]

/-- The number of colliding assignments is controlled by the sum of the
four explicit prime-equation budgets. -/
theorem card_tangentCollisionConfigurations_le_endpointBudget
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (collision : TangentCollisionIndex Request) :
    (tangentCollisionConfigurations
      (lists := lists) source target collision).card ≤
      tangentCollisionEndpointBudget N source target collision := by
  refine (card_tangentCollisionConfigurations_le_fourEndpointEquations
    (lists := lists) source target collision).trans ?_
  exact Finset.sum_le_sum fun leftSide _hleft ↦
    Finset.sum_le_sum fun rightSide _hright ↦
      (card_tangentEndpointEquationConfigurations_le_solutions
        (lists := lists) source target collision leftSide rightSide).trans
        (card_tangentEndpointEquationSolutions_prime_le_budget
          (hprime _ leftSide) (hprime _ rightSide)
          (fun multiplier hmultiplier ↦
            hupper _ leftSide multiplier hmultiplier))

/-! ## From list cardinalities to pair probabilities -/



theorem tangentCollisionLowerChoiceCount_pos
    {Request : Type*} (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (collision : TangentCollisionIndex Request) :
    0 < tangentCollisionLowerChoiceCount lowerCard collision := by
  exact Finset.prod_pos fun request _hrequest ↦ hlowerPos request.1

theorem tangentCollisionLowerChoiceCount_le_choiceCount
    {Request : Type*} {lists : Request → Finset ℕ}
    (lowerCard : Request → ℕ)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionLowerChoiceCount lowerCard collision ≤
      tangentCollisionChoiceCount (lists := lists) collision := by
  exact Finset.prod_le_prod
    (fun _request _hrequest ↦ Nat.zero_le _)
    (fun request _hrequest ↦ hlower request.1)

/-- Probability estimate obtained only from the four equation counts and
request-wise list cardinality lower bounds. -/
theorem tangentCollisionProbability_le_endpointBudget_div_lowerChoiceCount
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionProbability lists hlist source target collision ≤
      (tangentCollisionEndpointBudget N source target collision : ℝ) /
        tangentCollisionLowerChoiceCount lowerCard collision := by
  rw [tangentCollisionProbability_eq_configurationCount_div]
  calc
    ((tangentCollisionConfigurations
          (lists := lists) source target collision).card : ℝ) /
        tangentCollisionChoiceCount (lists := lists) collision ≤
      (tangentCollisionEndpointBudget N source target collision : ℝ) /
        tangentCollisionChoiceCount (lists := lists) collision := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tangentCollisionConfigurations_le_endpointBudget
        (lists := lists) N source target hprime hupper collision
    _ ≤ (tangentCollisionEndpointBudget N source target collision : ℝ) /
        tangentCollisionLowerChoiceCount lowerCard collision := by
      apply div_le_div_of_nonneg_left (by positivity)
      · exact_mod_cast tangentCollisionLowerChoiceCount_pos
          lowerCard hlowerPos collision
      · exact_mod_cast tangentCollisionLowerChoiceCount_le_choiceCount
          (lists := lists) lowerCard hlower collision

/-! ## Exact reindexing of an incident-event sum -/





theorem tangentIncidentOtherRequest_mem_erase
    {Request : Type*} [DecidableEq Request]
    {request : Request} {collision : TangentCollisionIndex Request}
    (hrequest : request ∈ collision.1) :
    tangentIncidentOtherRequest request collision ∈
      collision.1.erase request := by
  simp only [tangentIncidentOtherRequest, dif_pos hrequest]
  exact (tangentIncidentErase_nonempty hrequest).choose_spec

theorem tangentIncidentOtherRequest_ne
    {Request : Type*} [DecidableEq Request]
    {request : Request} {collision : TangentCollisionIndex Request}
    (hrequest : request ∈ collision.1) :
    tangentIncidentOtherRequest request collision ≠ request := by
  exact Finset.ne_of_mem_erase
    (tangentIncidentOtherRequest_mem_erase hrequest)

theorem tangentIncidentSupport_eq_pair
    {Request : Type*} [DecidableEq Request]
    {request : Request} {collision : TangentCollisionIndex Request}
    (hrequest : request ∈ collision.1) :
    collision.1 = {request, tangentIncidentOtherRequest request collision} := by
  have hcard : (collision.1.erase request).card = 1 := by
    rw [Finset.card_erase_of_mem hrequest, collision.2]
  obtain ⟨other, hother⟩ := Finset.card_eq_one.mp hcard
  have hchosen := tangentIncidentOtherRequest_mem_erase hrequest
  rw [hother] at hchosen
  have hchosenEq : tangentIncidentOtherRequest request collision = other := by
    simpa only [Finset.mem_singleton] using hchosen
  rw [← Finset.insert_erase hrequest, hother, hchosenEq]



/-- On the pair collision index, the internal support ordering gives the
same (symmetric) four-equation budget as the displayed ordered pair. -/
theorem tangentCollisionEndpointBudget_pair
    {Request : Type*} [DecidableEq Request]
    (N : ℕ) (source target : Request → ℕ)
    (left right : Request) (hne : left ≠ right) :
    tangentCollisionEndpointBudget N source target
        (tangentCollisionIndexOfDistinctRequests left right hne) =
      tangentOrderedPairEndpointBudget N source target left right := by
  let collision := tangentCollisionIndexOfDistinctRequests left right hne
  have hfirst : (tangentCollisionFirstRequest collision).1 = left ∨
      (tangentCollisionFirstRequest collision).1 = right := by
    have hmem := (tangentCollisionFirstRequest collision).2
    simpa only [collision, tangentCollisionIndexOfDistinctRequests,
      Finset.mem_insert, Finset.mem_singleton] using hmem
  have hsecond : (tangentCollisionSecondRequest collision).1 = left ∨
      (tangentCollisionSecondRequest collision).1 = right := by
    have hmem := (tangentCollisionSecondRequest collision).2
    simpa only [collision, tangentCollisionIndexOfDistinctRequests,
      Finset.mem_insert, Finset.mem_singleton] using hmem
  change tangentOrderedPairEndpointBudget N source target
      (tangentCollisionFirstRequest collision).1
      (tangentCollisionSecondRequest collision).1 =
    tangentOrderedPairEndpointBudget N source target left right
  rcases hfirst with hfirst | hfirst <;>
    rcases hsecond with hsecond | hsecond
  · exact (tangentCollisionFirstRequest_ne_secondRequest collision
      (Subtype.ext (hfirst.trans hsecond.symm))).elim
  · rw [hfirst, hsecond]
  · rw [hfirst, hsecond]
    exact tangentOrderedPairEndpointBudget_comm
      N source target right left
  · exact (tangentCollisionFirstRequest_ne_secondRequest collision
      (Subtype.ext (hfirst.trans hsecond.symm))).elim

/-- On an ordered pair, the supported product is literally the product of
the two lower cardinalities. -/
theorem tangentCollisionLowerChoiceCount_pair
    {Request : Type*} [DecidableEq Request]
    (lowerCard : Request → ℕ) (left right : Request) (hne : left ≠ right) :
      tangentCollisionLowerChoiceCount lowerCard
        (tangentCollisionIndexOfDistinctRequests left right hne) =
      lowerCard left * lowerCard right := by
  rw [tangentCollisionLowerChoiceCount, Finset.prod_coe_sort]
  change (∏ request ∈ ({left, right} : Finset Request),
      lowerCard request) = lowerCard left * lowerCard right
  simp only [Finset.prod_insert, Finset.prod_singleton,
    Finset.mem_singleton, hne, not_false_eq_true]





/-- The incident collision sum is exactly the sum over all other requests;
there is no factor two and no double counting in this reindexing. -/
theorem tangentRequestCollisionMass_eq_sum_otherRequests
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ) (request : Request) :
    tangentRequestCollisionMass lists hlist source target request =
      ∑ other ∈ Finset.univ.erase request,
        tangentPairCollisionProbability lists hlist source target
          request other := by
  classical
  unfold tangentRequestCollisionMass tangentIncidentCollisions
  apply Finset.sum_bij
    (fun collision _hcollision ↦
      tangentIncidentOtherRequest request collision)
  · intro collision hcollision
    have hrequest := (Finset.mem_filter.mp hcollision).2
    exact Finset.mem_erase.mpr ⟨
      tangentIncidentOtherRequest_ne hrequest,
      Finset.mem_univ _⟩
  · intro left hleft right hright hother
    apply Subtype.ext
    have hleftRequest := (Finset.mem_filter.mp hleft).2
    have hrightRequest := (Finset.mem_filter.mp hright).2
    rw [tangentIncidentSupport_eq_pair hleftRequest,
      tangentIncidentSupport_eq_pair hrightRequest, hother]
  · intro other hother
    have hne : request ≠ other := by
      exact (Finset.mem_erase.mp hother).1.symm
    let collision := tangentCollisionIndexOfDistinctRequests
      request other hne
    have hrequestMem : request ∈ collision.1 := by
      simp only [collision, tangentCollisionIndexOfDistinctRequests,
        Finset.mem_insert, Finset.mem_singleton, true_or]
    have hcollision : collision ∈
        Finset.univ.filter fun event : TangentCollisionIndex Request ↦
          request ∈ event.1 := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrequestMem⟩
    refine ⟨collision, hcollision, ?_⟩
    have hmem := tangentIncidentOtherRequest_mem_erase
      (collision := collision) (request := request) hrequestMem
    have herase : collision.1.erase request = {other} := by
      ext candidate
      simp only [collision, tangentCollisionIndexOfDistinctRequests,
        Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_hneRequest, hcandidate⟩
        exact hcandidate.resolve_left _hneRequest
      · intro hcandidate
        subst candidate
        exact ⟨hne.symm, Or.inr rfl⟩
    rw [herase] at hmem
    exact Finset.mem_singleton.mp hmem
  · intro collision hcollision
    have hrequest := (Finset.mem_filter.mp hcollision).2
    have hne : request ≠ tangentIncidentOtherRequest request collision :=
      (tangentIncidentOtherRequest_ne hrequest).symm
    simp only [tangentPairCollisionProbability, dif_pos hne]
    congr 1
    apply Subtype.ext
    exact tangentIncidentSupport_eq_pair hrequest

/-! ## Request loads and the literal `1/8` terminal -/













theorem tangentOtherRequestLabelLoad_le_fullLoad
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (source target : Request → ℕ) (anchor : Request) (label : ℕ) :
    tangentOtherRequestLabelLoad source target anchor label ≤
      tangentRequestLabelLoad source target label := by
  apply Finset.card_le_card
  intro request hrequest
  have hdata : request ∈ Finset.univ.erase anchor ∧
      tangentRequestHasLabel source target label request :=
    Finset.mem_filter.mp hrequest
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdata.2⟩

theorem tangentOtherRequestCount_le_requestCount
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (anchor : Request) :
    tangentOtherRequestCount anchor ≤ tangentTotalRequestCount Request := by
  unfold tangentOtherRequestCount tangentTotalRequestCount
  rw [Finset.card_erase_of_mem (Finset.mem_univ anchor),
    Finset.card_univ]
  exact Nat.sub_le _ _

/-- Sum of a label indicator is exactly the corresponding request load. -/
theorem sum_tangentRequestHasLabel_indicator
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (source target : Request → ℕ) (anchor : Request) (label : ℕ)
    (charge : ℝ) :
    ∑ other ∈ Finset.univ.erase anchor,
        (if tangentRequestHasLabel source target label other
        then charge else (0 : ℝ)) =
      (tangentOtherRequestLabelLoad source target anchor label : ℝ) *
        charge := by
  classical
  rw [← Finset.sum_filter]
  simp [tangentOtherRequestLabelLoad, Finset.sum_const,
    nsmul_eq_mul]

/-- Abstract load summation.  A disjoint-label charge is paid for every
other request, while a shared-label surcharge is paid only on requests
incident to either endpoint label of the fixed request. -/
theorem tangentRequestCollisionMass_le_loadBudget
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hpair : ∀ left right, left ≠ right →
      tangentPairCollisionProbability lists hlist source target left right ≤
        disjointCharge +
          (if tangentRequestHasLabel source target (source left) right
            then sharedCharge (source left) else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then sharedCharge (target left) else 0))
    (request : Request) :
    tangentRequestCollisionMass lists hlist source target request ≤
      (tangentOtherRequestCount request : ℝ) * disjointCharge +
        (tangentOtherRequestLabelLoad source target request
          (source request) : ℝ) * sharedCharge (source request) +
        (tangentOtherRequestLabelLoad source target request
          (target request) : ℝ) * sharedCharge (target request) := by
  rw [tangentRequestCollisionMass_eq_sum_otherRequests]
  calc
    (∑ other ∈ Finset.univ.erase request,
        tangentPairCollisionProbability lists hlist source target
          request other) ≤
      ∑ other ∈ Finset.univ.erase request,
        (disjointCharge +
          (if tangentRequestHasLabel source target (source request) other
            then sharedCharge (source request) else 0) +
          (if tangentRequestHasLabel source target (target request) other
            then sharedCharge (target request) else 0)) := by
      apply Finset.sum_le_sum
      intro other hother
      exact hpair request other (Finset.mem_erase.mp hother).1.symm
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [sum_tangentRequestHasLabel_indicator,
        sum_tangentRequestHasLabel_indicator]
      simp [tangentOtherRequestCount, Finset.sum_const, nsmul_eq_mul]

/-- Paper-facing version using the full loads `K_req`, `k_u`, and `k_v`.
The other-request version above is slightly sharper. -/
theorem tangentRequestCollisionMass_le_fullLoadBudget
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hdisjointNonneg : 0 ≤ disjointCharge)
    (hsharedNonneg : ∀ label, 0 ≤ sharedCharge label)
    (hpair : ∀ left right, left ≠ right →
      tangentPairCollisionProbability lists hlist source target left right ≤
        disjointCharge +
          (if tangentRequestHasLabel source target (source left) right
            then sharedCharge (source left) else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then sharedCharge (target left) else 0))
    (request : Request) :
    tangentRequestCollisionMass lists hlist source target request ≤
      (tangentTotalRequestCount Request : ℝ) * disjointCharge +
        (tangentRequestLabelLoad source target
          (source request) : ℝ) * sharedCharge (source request) +
        (tangentRequestLabelLoad source target
          (target request) : ℝ) * sharedCharge (target request) := by
  refine (tangentRequestCollisionMass_le_loadBudget
    lists hlist source target disjointCharge sharedCharge hpair request).trans ?_
  apply add_le_add
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ hdisjointNonneg
      exact_mod_cast tangentOtherRequestCount_le_requestCount request
    · apply mul_le_mul_of_nonneg_right _ (hsharedNonneg (source request))
      exact_mod_cast tangentOtherRequestLabelLoad_le_fullLoad
        source target request (source request)
  · apply mul_le_mul_of_nonneg_right _ (hsharedNonneg (target request))
    exact_mod_cast tangentOtherRequestLabelLoad_le_fullLoad
      source target request (target request)

/-- The pairwise endpoint-counting estimate obtained from the exact finite
cardinality hypotheses, packaged in the totalized ordered-pair notation. -/
theorem tangentPairCollisionProbability_le_endpointBudget
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (left right : Request) (hne : left ≠ right) :
    tangentPairCollisionProbability lists hlist source target left right ≤
      (tangentCollisionEndpointBudget N source target
          (tangentCollisionIndexOfDistinctRequests left right hne) : ℝ) /
        tangentCollisionLowerChoiceCount lowerCard
          (tangentCollisionIndexOfDistinctRequests left right hne) := by
  rw [tangentPairCollisionProbability, dif_pos hne]
  exact tangentCollisionProbability_le_endpointBudget_div_lowerChoiceCount
    lists hlist lowerCard hlowerPos hlower N source target
      hprime hupper _



/-- Pair probability is bounded by the totalized exact counting quotient. -/
theorem tangentPairCollisionProbability_le_budgetQuotient
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (left right : Request) :
    tangentPairCollisionProbability lists hlist source target left right ≤
      tangentPairEndpointBudgetQuotient lowerCard N source target left right := by
  by_cases hne : left ≠ right
  · rw [tangentPairEndpointBudgetQuotient, dif_pos hne]
    simpa only [tangentCollisionEndpointBudget_pair,
      tangentCollisionLowerChoiceCount_pair, Nat.cast_mul] using
      tangentPairCollisionProbability_le_endpointBudget
      lists hlist lowerCard hlowerPos hlower N source target
        hprime hupper left right hne
  · rw [tangentPairEndpointBudgetQuotient, dif_neg hne,
      tangentPairCollisionProbability, dif_neg hne]



/-! ## Specialization to the actual clean common lists -/

/-- Every endpoint of an actual clean-list member is below the broad cutoff.
This is a deterministic consequence of membership in the literal interval. -/
theorem tangentCleanMultiplierLists_endpoint_le_broadUpper
    {Request : Type*}
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hpositive : ∀ request,
      0 < source request ∧ 0 < target request)
    (request : Request) (side : TangentEndpointSide)
    (multiplier : ℕ)
    (hmultiplier : multiplier ∈
      tangentCleanMultiplierLists n K h Phead X0 y source target
        dedicatedRows numericalGuards request) :
    tangentEndpointLabel source target side request * multiplier ≤
      tangentBroadUpper n K h := by
  have hdata := mem_tangentCleanCommonMultiplierList.mp hmultiplier
  have hmaxPos : 0 < max (source request) (target request) := by
    exact lt_of_lt_of_le (hpositive request).1 (le_max_left _ _)
  have hmaxUpper : max (source request) (target request) * multiplier ≤
      tangentBroadUpper n K h := by
    have hbound := (Nat.le_div_iff_mul_le hmaxPos).mp hdata.1.2
    simpa only [Nat.mul_comm] using hbound
  cases side
  · exact (Nat.mul_le_mul_right multiplier (le_max_left _ _)).trans
      hmaxUpper
  · exact (Nat.mul_le_mul_right multiplier (le_max_right _ _)).trans
      hmaxUpper













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentSplitRequestLoads -/
section


/-!
# Actual request loads for the split tangent flow

This file instantiates the abstract collision-counting loads on the literal
request type

`Sigma e : edges, Fin (max 1 (ceil (4 * L * flow e / sigma)))`.

There are no request-count or collision-mass hypotheses below.  The total
load `K_req` is identified with the sum of the edge splitting counts, and
the label load `k_p` is identified with the same sum restricted to edges
incident to `p`.  The ceiling estimates then express both loads in terms of
the actual total/incident flow masses and support census.

The last layer substitutes those proved loads into
`tangentRequestCollisionMass_le_fullLoadBudget`.  It is deliberately
normalized in the paper's form

`K_req / n`, `p * k_p / n`.

For the actual paper guard set, the sharp bank census is recorded alongside
this load calculation.  The only list input retained by the collision
terminal is the exact request-wise cardinality lower bound; no analytic
density estimate is hidden here.

The paper-specialized terminals deliberately retain the following separate
mathematical inputs.  The sharp finite-deletion ledger does **not** itself
prove them.

* `hlowerPos` and `hlower`: a positive exact lower bound for every clean
  request list;
* `hpairArithmetic`: the explicit four-equation quotient comparison with
  the chosen shared/disjoint charges;
* either the literal flow-budget inequality, or proved total-traffic,
  incident-traffic, and support censuses;
* the final displayed flow/census budget inequality `≤ 1/8`.

Thus this module derives request loads from those flow censuses and passes
them to the proved counting/LLL terminal, but does not claim the still
missing analytic list density, earthmover census, or final parameter
arithmetic.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Exact reindexing of split requests -/



/-- The abstract paper load `K_req`, on the actual split-request type, is
literally the sum of the edge splitting counts. -/
theorem tangentSplitTotalRequestCount_eq_requestTotal
    {E : Type*} (edges : Finset E) (L sigma : ℝ) (flow : E → ℝ) :
    tangentTotalRequestCount (TangentSplitRequest edges L sigma flow) =
      tangentRequestTotal edges L sigma flow := by
  unfold tangentTotalRequestCount
  exact card_tangentSplitRequest edges L sigma flow

/-- The abstract label load `k_p`, on the actual split-request type, is
literally the sum of splitting counts over edges incident to `p`. -/
theorem tangentSplitRequestLabelLoad_eq_incidentRequestCount
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ) (label : ℕ) :
    tangentRequestLabelLoad
        (tangentSplitRequestSource
          (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
        (tangentSplitRequestTarget
          (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
        label =
      tangentIncidentRequestCount edges source target L sigma flow label := by
  classical
  rw [tangentRequestLabelLoad, ← Fintype.card_subtype]
  calc
    Fintype.card
        {request : TangentSplitRequest edges L sigma flow //
          tangentRequestHasLabel
            (tangentSplitRequestSource source)
            (tangentSplitRequestTarget target) label request} =
        Fintype.card
          (TangentSplitRequest
            (tangentIncidentEdges edges source target label)
              L sigma flow) :=
      Fintype.card_congr
        (tangentIncidentSplitRequestEquiv
          edges source target L sigma flow label)
    _ = tangentRequestTotal
          (tangentIncidentEdges edges source target label) L sigma flow :=
      card_tangentSplitRequest
        (tangentIncidentEdges edges source target label) L sigma flow
    _ = tangentIncidentRequestCount
          edges source target L sigma flow label := rfl

/-- The incident support degree is bounded by the complete support census.
This is the exact finite version of the harmless `+1`-per-edge ledger. -/
theorem tangentSupportDegree_le_edges_card
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P) (label : P) :
    tangentSupportDegree edges source target label ≤ edges.card := by
  unfold tangentSupportDegree tangentIncidentEdges
  exact Finset.card_filter_le _ _



/-! ## The literal strictly-positive flow support -/





/-- On a globally nonnegative directed flow, restricting to the strictly
positive support preserves total traffic exactly. -/
theorem sum_tangentPositiveFlowEdges_eq_traffic
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V → V → ℝ) (hflow : ∀ source target, 0 ≤ flow source target) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2) = tangentFlowTraffic flow := by
  classical
  calc
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2) =
      ∑ edge : V × V, flow edge.1 edge.2 := by
        apply Finset.sum_subset
          (Finset.subset_univ (tangentPositiveFlowEdges flow))
        intro edge _hedge hedge
        have hnotPos : ¬0 < flow edge.1 edge.2 := by
          simpa only [mem_tangentPositiveFlowEdges] using hedge
        have hzero : flow edge.1 edge.2 = 0 :=
          le_antisymm (le_of_not_gt hnotPos) (hflow edge.1 edge.2)
        exact hzero
    _ = tangentFlowTraffic flow := by
      rw [tangentFlowTraffic, Fintype.sum_prod_type]

/-! ## The actual total and incident request upper bounds -/





/-- The literal split-request count is bounded by its real ceiling ledger. -/
theorem cast_tangentSplitTotalRequestCount_le_upper
    {E : Type*} (edges : Finset E) {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentTotalRequestCount
      (TangentSplitRequest edges L sigma flow) : ℝ) ≤
        tangentSplitTotalRequestUpper edges L sigma flow := by
  rw [tangentSplitTotalRequestCount_eq_requestTotal]
  exact cast_tangentRequestTotal_le edges flow hflow hL hsigma

/-- The literal load at one label is bounded by its incident-flow ceiling
ledger. -/
theorem cast_tangentSplitRequestLabelLoad_le_upper
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma) (label : ℕ) :
    (tangentRequestLabelLoad
      (tangentSplitRequestSource
        (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
      (tangentSplitRequestTarget
        (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
      label : ℝ) ≤
        tangentSplitLabelRequestUpper
          edges source target L sigma flow label := by
  rw [tangentSplitRequestLabelLoad_eq_incidentRequestCount]
  exact cast_tangentIncidentRequestCount_le
    edges source target flow hflow hL hsigma label







/-! ## Paper normalization `K_req/n` and `p*k_p/n` -/









/-! ## Substitution of literal flow and support censuses -/













/-! ## Substitution in the full collision-load budget -/





/-- Substituting larger traffic and support censuses can only increase the
normalized collision budget. -/
theorem tangentSplitNormalizedCollisionFlowBudget_le_censusBudget
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request ≤
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          disjointCoefficient sharedCoefficient request := by
  have htotal : tangentSplitTotalRequestUpper edges L sigma flow ≤
      tangentSplitCensusTotalRequestUpper
        L sigma totalTraffic supportCount := by
    unfold tangentSplitTotalRequestUpper
      tangentSplitCensusTotalRequestUpper
    exact add_le_add
      (mul_le_mul_of_nonneg_left htraffic (by positivity))
      (by exact_mod_cast hsupport)
  have hlabel : ∀ label,
      tangentSplitLabelRequestUpper
          edges source target L sigma flow label ≤
        tangentSplitCensusLabelRequestUpper
          L sigma incidentTraffic supportCount label := by
    intro label
    unfold tangentSplitLabelRequestUpper
      tangentSplitCensusLabelRequestUpper
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hincident label) (by positivity))
      (by
        exact_mod_cast
          (tangentSupportDegree_le_edges_card
            edges source target label).trans hsupport)
  unfold tangentSplitNormalizedCollisionFlowBudget
    tangentSplitNormalizedTotalRequestUpper
    tangentSplitNormalizedLabelRequestUpper
    tangentSplitNormalizedCollisionCensusBudget
  apply add_le_add
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ hdisjointCoefficient
      exact div_le_div_of_nonneg_right htotal (Nat.cast_nonneg n)
    · apply mul_le_mul_of_nonneg_right _ hsharedCoefficient
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact mul_le_mul_of_nonneg_left
        (hlabel (tangentSplitRequestSource source request))
        (Nat.cast_nonneg _)
  · apply mul_le_mul_of_nonneg_right _ hsharedCoefficient
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_left
      (hlabel (tangentSplitRequestTarget target request))
      (Nat.cast_nonneg _)

/-- The abstract full-load collision estimate specialized to the literal
split request family.  Both `K_req` and the two `k_p` terms are eliminated
in favor of the proved edge-flow ledgers above. -/
theorem tangentSplitRequestCollisionMass_le_normalizedFlowBudget
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (lists : TangentSplitRequest edges L sigma flow → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpair : ∀ left right, left ≠ right →
      tangentPairCollisionProbability lists hlist
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source left) right
            then sharedCoefficient *
                tangentSplitRequestSource source left / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target left) right
            then sharedCoefficient *
                tangentSplitRequestTarget target left / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentRequestCollisionMass lists hlist
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) request ≤
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request := by
  let disjointCharge : ℝ := disjointCoefficient / n
  let sharedCharge : ℕ → ℝ := fun label ↦
    sharedCoefficient * label / n
  have hdisjointCharge : 0 ≤ disjointCharge := by
    exact div_nonneg hdisjointCoefficient (Nat.cast_nonneg n)
  have hsharedCharge : ∀ label, 0 ≤ sharedCharge label := by
    intro label
    exact div_nonneg
      (mul_nonneg hsharedCoefficient (Nat.cast_nonneg label))
      (Nat.cast_nonneg n)
  have hfull := tangentRequestCollisionMass_le_fullLoadBudget
    lists hlist
      (tangentSplitRequestSource source)
      (tangentSplitRequestTarget target)
      disjointCharge sharedCharge hdisjointCharge hsharedCharge
      (by
        intro left right hne
        simpa only [disjointCharge, sharedCharge] using
          hpair left right hne)
      request
  have htotal := cast_tangentSplitTotalRequestCount_le_upper
    edges flow hflow hL hsigma
  have hsource := cast_tangentSplitRequestLabelLoad_le_upper
    edges source target flow hflow hL hsigma
      (tangentSplitRequestSource source request)
  have htarget := cast_tangentSplitRequestLabelLoad_le_upper
    edges source target flow hflow hL hsigma
      (tangentSplitRequestTarget target request)
  calc
    tangentRequestCollisionMass lists hlist
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) request ≤
      (tangentTotalRequestCount
          (TangentSplitRequest edges L sigma flow) : ℝ) *
          disjointCharge +
        (tangentRequestLabelLoad
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          (tangentSplitRequestSource source request) : ℝ) *
            sharedCharge (tangentSplitRequestSource source request) +
        (tangentRequestLabelLoad
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          (tangentSplitRequestTarget target request) : ℝ) *
            sharedCharge (tangentSplitRequestTarget target request) := hfull
    _ ≤ tangentSplitTotalRequestUpper edges L sigma flow *
          disjointCharge +
        tangentSplitLabelRequestUpper edges source target L sigma flow
            (tangentSplitRequestSource source request) *
          sharedCharge (tangentSplitRequestSource source request) +
        tangentSplitLabelRequestUpper edges source target L sigma flow
            (tangentSplitRequestTarget target request) *
          sharedCharge (tangentSplitRequestTarget target request) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_right htotal hdisjointCharge)
          (mul_le_mul_of_nonneg_right hsource
            (hsharedCharge (tangentSplitRequestSource source request))))
        (mul_le_mul_of_nonneg_right htarget
          (hsharedCharge (tangentSplitRequestTarget target request)))
    _ = tangentSplitNormalizedCollisionFlowBudget
          n edges source target L sigma flow
            disjointCoefficient sharedCoefficient request := by
      simp only [disjointCharge, sharedCharge,
        tangentSplitNormalizedCollisionFlowBudget,
        tangentSplitNormalizedTotalRequestUpper,
        tangentSplitNormalizedLabelRequestUpper]
      ring



/-! ## Exact clean-list counting plus the proved load ledger -/

/-- For the literal clean common lists, exact list cardinality lower bounds
and four-equation arithmetic imply the expanded flow-side collision bound.
The actual `K_req` and `k_p` bounds are proved by the preceding theorem and
are not premises here. -/
theorem tangentCleanSplitRequestCollisionMass_le_normalizedFlowBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source left) right
            then sharedCoefficient *
                tangentSplitRequestSource source left / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target left) right
            then sharedCoefficient *
                tangentSplitRequestTarget target left / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentRequestCollisionMass
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards)
        (fun request ↦ Finset.card_pos.mp
          ((hlowerPos request).trans_le (hlower request)))
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) request ≤
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request := by
  let lists := tangentSplitCleanMultiplierLists
    edges source target L sigma flow n K h Phead X0 y
      dedicatedRows numericalGuards
  let hlist : ∀ request, (lists request).Nonempty := fun request ↦
    Finset.card_pos.mp ((hlowerPos request).trans_le (hlower request))
  apply tangentSplitRequestCollisionMass_le_normalizedFlowBudget
    n edges source target flow lists hlist
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient
  · intro left right hne
    apply (tangentPairCollisionProbability_le_budgetQuotient
      lists hlist lowerCard hlowerPos
        (by
          intro request
          simpa only [lists] using hlower request)
        (tangentBroadUpper n K h)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target)
        (by
          intro request side
          cases side with
          | source =>
              simpa only [tangentEndpointLabel,
                tangentSplitRequestSource, tangentSplitRequestEdge] using
                (hprime request.1.1 request.1.2).1
          | target =>
              simpa only [tangentEndpointLabel,
                tangentSplitRequestTarget, tangentSplitRequestEdge] using
                (hprime request.1.1 request.1.2).2)
        (by
          intro request side multiplier hmultiplier
          simpa only [lists, tangentSplitCleanMultiplierLists] using
            tangentCleanMultiplierLists_endpoint_le_broadUpper
              n K h Phead X0 y
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              dedicatedRows numericalGuards
              (by
                intro splitRequest
                exact ⟨
                  (hprime splitRequest.1.1 splitRequest.1.2).1.pos,
                  (hprime splitRequest.1.1 splitRequest.1.2).2.pos⟩)
              request side multiplier hmultiplier)
        left right).trans
    rw [tangentPairEndpointBudgetQuotient, dif_pos hne]
    exact hpairArithmetic left right hne
  · exact hflow
  · exact hL
  · exact hsigma

/-- The literal `1/8` terminal.  Its last premise is the displayed
flow/degree arithmetic, not a request-load bound and not a collision-mass
bound. -/
theorem tangentCleanSplitRequestCollisionMass_le_eighth_of_flowBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source left) right
            then sharedCoefficient *
                tangentSplitRequestSource source left / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target left) right
            then sharedCoefficient *
                tangentSplitRequestTarget target left / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∀ request,
      tangentRequestCollisionMass
          (tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 y
              dedicatedRows numericalGuards)
          (fun request ↦ Finset.card_pos.mp
            ((hlowerPos request).trans_le (hlower request)))
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) request ≤ 1 / 8 := by
  intro request
  exact (tangentCleanSplitRequestCollisionMass_le_normalizedFlowBudget
    n K h Phead X0 y edges source target flow
      dedicatedRows numericalGuards lowerCard hlowerPos hlower hprime
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpairArithmetic
      hflow hL hsigma request).trans (hbudget request)



/-- Collision-free common multipliers for the actual split request type,
with all request-load bounds discharged by the flow ledger. -/
theorem tangentSplitEndpointsDistinct_of_normalizedFlowBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ edge ∈ edges, source edge ≠ target edge)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source left) right
            then sharedCoefficient *
                tangentSplitRequestSource source left / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target left) right
            then sharedCoefficient *
                tangentSplitRequestTarget target left / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 y
              dedicatedRows numericalGuards request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) multiplier := by
  let hlist : ∀ request,
      (tangentSplitCleanMultiplierLists
        edges source target L sigma flow n K h Phead X0 y
          dedicatedRows numericalGuards request).Nonempty := fun request ↦
    Finset.card_pos.mp ((hlowerPos request).trans_le (hlower request))
  apply tangentSplitEndpointsDistinct_of_cleanRequestMass
    edges source target L sigma flow n K h Phead X0 y
      dedicatedRows numericalGuards
  · intro request
    simpa only [tangentSplitRequestSource, tangentSplitRequestTarget,
      tangentSplitRequestEdge] using
        hsourceTarget request.1.1 request.1.2
  · exact tangentCleanSplitRequestCollisionMass_le_eighth_of_flowBudget
      n K h Phead X0 y edges source target flow
        dedicatedRows numericalGuards lowerCard hlowerPos hlower hprime
        disjointCoefficient sharedCoefficient
        hdisjointCoefficient hsharedCoefficient hpairArithmetic
        hflow hL hsigma hbudget

/-- Collision-free split endpoints after replacing the literal flow ledger
by proved total-traffic, incident-traffic, and sparse-support censuses.  No
request-count or collision-mass bound occurs among the premises. -/
theorem tangentSplitEndpointsDistinct_of_normalizedCensusBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ edge ∈ edges, source edge ≠ target edge)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source left) right
            then sharedCoefficient *
                tangentSplitRequestSource source left / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target left) right
            then sharedCoefficient *
                tangentSplitRequestTarget target left / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount)
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 y
              dedicatedRows numericalGuards request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) multiplier := by
  apply tangentSplitEndpointsDistinct_of_normalizedFlowBudget
    n K h Phead X0 y edges source target flow
      dedicatedRows numericalGuards hsourceTarget
      lowerCard hlowerPos hlower hprime
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpairArithmetic
      hflow hL hsigma
  intro request
  exact (tangentSplitNormalizedCollisionFlowBudget_le_censusBudget
    n edges source target flow totalTraffic incidentTraffic supportCount
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hL hsigma
      htraffic hincident hsupport request).trans (hbudget request)

/-! ## The actual sharp paper bank and row census -/

namespace BankPaperRealization





/-- Actual-paper bank/guard specialization with the split-request loads
discharged by external total-traffic, incident-traffic, and sparse-support
censuses.  The exact request-wise list lower bound remains explicit. -/
theorem tangentPaperSplitEndpointsDistinct_of_normalizedCensusBudget
    {c : ℝ} {depth n M : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    {E : Type*} [DecidableEq E]
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (K h Phead X0 : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (hsourceTarget : ∀ edge ∈ edges, source edge ≠ target edge)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ leftRequest rightRequest,
      ∀ _hne : leftRequest ≠ rightRequest,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          leftRequest rightRequest : ℝ) /
          (lowerCard leftRequest * lowerCard rightRequest) ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source leftRequest) rightRequest
            then sharedCoefficient *
                tangentSplitRequestSource source leftRequest / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target leftRequest) rightRequest
            then sharedCoefficient *
                tangentSplitRequestTarget target leftRequest / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount)
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) multiplier := by
  exact tangentSplitEndpointsDistinct_of_normalizedCensusBudget
    n K h Phead X0 (yNat n) edges source target flow
      R.tangentPaperDedicatedRows
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      hsourceTarget lowerCard hlowerPos hlower hprime
      totalTraffic incidentTraffic supportCount
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpairArithmetic
      hflow hL hsigma htraffic hincident hsupport hbudget

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPairArithmetic -/
section


/-!
# Finite arithmetic for tangent collision pairs

This file discharges the finite four-endpoint part of the
`hpairArithmetic` contract in `TangentSplitRequestLoads`.  It separates two
layers.

* Four per-equation bounds are assembled into the paper's one disjoint charge
  and two possible shared-label charges.  Distinct endpoints on the right
  request ensure that each left label can create at most one shared equation.
* A paper-scale specialization derives the per-equation bounds from a supplied
  effective list-density inequality

  `density * n <= lowerCard(request) * endpointLabel(request, side)`.

The specialization uses only `tangentBroadUpper n K h <= 2*n`, prime-label
positivity, and explicit hypotheses saying that every endpoint is at most a
cutoff whose first and second powers are at most `n`.  It yields the concrete
coefficients `12 / density^2` and `3 / density^2`.

No clean-list density estimate or cutoff asymptotic is proved here.  In a
paper application those are precisely the inputs needed to establish the
displayed effective-density and cutoff inequalities.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Coefficients and elementary endpoint budgets -/





/-- The disjoint-label density coefficient is nonnegative at nonnegative
density. -/
theorem tangentDensityDisjointCoefficient_nonneg
    {density : ℝ} (_hdensity : 0 ≤ density) :
    0 ≤ tangentDensityDisjointCoefficient density := by
  unfold tangentDensityDisjointCoefficient
  positivity

/-- The shared-label density coefficient is nonnegative at nonnegative
density. -/
theorem tangentDensitySharedCoefficient_nonneg
    {density : ℝ} (_hdensity : 0 ≤ density) :
    0 ≤ tangentDensitySharedCoefficient density := by
  unfold tangentDensitySharedCoefficient
  positivity







/-! ## Assembly of four endpoint equations -/





/-! ## Effective-density bounds for one endpoint equation -/





/-! ## Paper-scale pair arithmetic -/





/-! ## The literal `1/8` coefficient arithmetic -/

/-- The coefficients above reduce the final `1/8` comparison to the single
smallness inequality `4*total + source + target <= density^2/24`. -/
theorem tangentDensityCollisionBudget_le_eighth
    {density totalTerm sourceTerm targetTerm : ℝ}
    (hdensity : 0 < density)
    (hsmall :
      4 * totalTerm + sourceTerm + targetTerm ≤ density ^ 2 / 24) :
    totalTerm * tangentDensityDisjointCoefficient density +
        sourceTerm * tangentDensitySharedCoefficient density +
        targetTerm * tangentDensitySharedCoefficient density ≤
      1 / 8 := by
  have hsq : 0 < density ^ 2 := sq_pos_of_pos hdensity
  unfold tangentDensityDisjointCoefficient tangentDensitySharedCoefficient
  rw [show totalTerm * (12 / density ^ 2) +
      sourceTerm * (3 / density ^ 2) +
      targetTerm * (3 / density ^ 2) =
        (12 * totalTerm + 3 * sourceTerm + 3 * targetTerm) /
          density ^ 2 by ring]
  apply (div_le_iff₀ hsq).2
  nlinarith

/-- Census-facing specialization of the preceding `1/8` arithmetic.  The
traffic, incident-traffic, and support estimates themselves remain explicit
inside `hsmall`. -/
theorem tangentSplitNormalizedCollisionCensusBudget_le_eighth_of_density
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {flow : E → ℝ}
    (L sigma totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ) (density : ℝ)
    (hdensity : 0 < density)
    (request : TangentSplitRequest edges L sigma flow)
    (hsmall :
      4 * (tangentSplitCensusTotalRequestUpper
            L sigma totalTraffic supportCount / n) +
        (((tangentSplitRequestSource (P := ℕ) source request : ℕ) : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma incidentTraffic
            supportCount (tangentSplitRequestSource source request) / n) +
        (((tangentSplitRequestTarget (P := ℕ) target request : ℕ) : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma incidentTraffic
            supportCount (tangentSplitRequestTarget target request) / n) ≤
          density ^ 2 / 24) :
    tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          (tangentDensityDisjointCoefficient density)
          (tangentDensitySharedCoefficient density) request ≤ 1 / 8 := by
  unfold tangentSplitNormalizedCollisionCensusBudget
  exact tangentDensityCollisionBudget_le_eighth hdensity hsmall

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentDistributedFlowCensus -/
section


/-!
# Distributed finite-band flow census

This file isolates the quantitative interface needed between a genuine
finite-band earthmover and the already formalized split-request collision
terminal.  Unlike the one-pivot star, a distributed earthmover records a
separate port load at every vertex.  Its two analytic ledgers are

* `traffic <= (1/2) * ||residual||_1 + 2 * cutTraffic`;
* `incident(label v) <= |residual v| + 2 * portLoad v`.

These are the literal estimates produced by the cell-boundary construction
in the paper.  They are strictly stronger than the final collision target
and do not mention a density or the constant `1 / 24`.

The module proves all consequences after those construction ledgers:

* positive support has at most `|V|^2` edges;
* the total split-request count and every endpoint-label request load have
  explicit upper bounds;
* fixed main/error/ceiling parameter budgets imply the exact existing guard
  `4*T + I_source + I_target <= density^2/24` for every request;
* hence the already proved `1/8` collision-census conclusion follows.

Existence of the cell earthmover is deliberately not postulated here.  It
must be constructed from band balance, prefix-load bounds, cell cardinality,
and adjacent-cell ratio geometry.  The downstream theorems keep every
construction estimate as a visible
hypothesis, so the unfinished construction cannot be confused with a
selector theorem or with the final collision target.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Residual, cut, and port ledgers -/









/-! ## Literal ratio-cell cuts and uniform adjacent-cell ports -/











































/-! ## Visible hypotheses for a distributed construction -/

/- The construction estimates are deliberately *not* bundled into a
structure.  The repository audit discipline forbids hiding a claimed
traffic or incident estimate in a conclusion-bearing certificate.  Every
generic theorem below therefore displays the exact flow property that it
uses. -/

/-! ## Support, locality, and literal traffic consequences -/

/-- The positive support of a finite directed flow has at most the quadratic
distributed-support census. -/
theorem card_tangentPositiveFlowEdges_le_distributedSupportCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) :
    (tangentPositiveFlowEdges flow).card <=
      tangentDistributedSupportCount V := by
  unfold tangentPositiveFlowEdges tangentDistributedSupportCount
  calc
    ((Finset.univ : Finset (V × V)).filter
        (fun edge => 0 < flow edge.1 edge.2)).card <=
        (Finset.univ : Finset (V × V)).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card V ^ 2 := by
      simp [pow_two]

/-- Injective vertex labels distinguish the endpoints of every positive
non-loop edge. -/
theorem tangentDistributedPositiveEdge_labels_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) {label : V -> Nat}
    (hpositiveEndpoints : forall {source target},
      0 < flow source target -> source ≠ target)
    (hlabel : Function.Injective label) {edge : V × V}
    (hedge : edge ∈ tangentPositiveFlowEdges flow) :
    tangentStarEdgeSource label edge ≠ tangentStarEdgeTarget label edge := by
  intro heq
  have hvertices : edge.1 = edge.2 := by
    apply hlabel
    simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using heq
  exact hpositiveEndpoints
    (mem_tangentPositiveFlowEdges.mp hedge) hvertices



/-- The total mass on the positive support is bounded by the declared traffic
ledger. -/
theorem sum_tangentDistributedPositiveEdges_le_trafficLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (residual : V -> Real) (cutTraffic : Real)
    (hflow : forall source target, 0 <= flow source target)
    (htraffic : tangentFlowTraffic flow <=
      tangentDistributedTotalTrafficLedger residual cutTraffic) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2) <=
      tangentDistributedTotalTrafficLedger residual cutTraffic := by
  rw [sum_tangentPositiveFlowEdges_eq_traffic flow hflow]
  exact htraffic

/-! ## Boundary preservation for an arbitrary distributed flow -/

/-- Restricting a nonnegative flow to its strictly positive support does not
change any weighted edge sum. -/
theorem sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (value : V × V -> Real) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * value edge) =
      ∑ edge : V × V, flow edge.1 edge.2 * value edge := by
  classical
  apply Finset.sum_subset
    (Finset.subset_univ (tangentPositiveFlowEdges flow))
  intro edge _hedge hedge
  have hnotPos : ¬0 < flow edge.1 edge.2 := by
    simpa only [mem_tangentPositiveFlowEdges] using hedge
  have hzero : flow edge.1 edge.2 = 0 :=
    le_antisymm (le_of_not_gt hnotPos) (hflow edge.1 edge.2)
  simp only [hzero, zero_mul]

/-- The positive support of a distributed earthmover has exactly the
prescribed residual boundary against every vertex test function. -/
theorem tangentDistributedPositiveEdges_boundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (value : V -> Real) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * (value edge.1 - value edge.2)) =
      ∑ v : V, residual v * value v := by
  calc
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * (value edge.1 - value edge.2)) =
      ∑ edge : V × V,
        flow edge.1 edge.2 * (value edge.1 - value edge.2) :=
      sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
        flow hflow
          (fun edge => value edge.1 - value edge.2)
    _ = ∑ source : V, ∑ target : V,
        flow source target * (value source - value target) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ v : V,
        tangentFlowDivergence flow v * value v :=
      tangentFlow_weightedBoundary_eq_divergence flow value
    _ = ∑ v : V, residual v * value v := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hdivergence v]

/-- Factorization-coordinate form of the distributed boundary. -/
theorem tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (p : Nat) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 *
          (((tangentStarEdgeSource label edge).factorization p : Real) -
            ((tangentStarEdgeTarget label edge).factorization p : Real))) =
      ∑ v : V, residual v * (label v).factorization p := by
  simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using
    tangentDistributedPositiveEdges_boundary_eq_residual
      flow residual hflow hdivergence
      (fun v => ((label v).factorization p : Real))

/-- Equal request splitting preserves the distributed residual boundary. -/
theorem tangentDistributedSplitRequest_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (L sigma : Real) (p : Nat) :
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge : V × V => flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : Real) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : Real))) =
      ∑ v : V, residual v * (label v).factorization p := by
  calc
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge : V × V => flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : Real) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : Real))) =
      ∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 *
          (((tangentStarEdgeSource label edge).factorization p : Real) -
            ((tangentStarEdgeTarget label edge).factorization p : Real)) := by
      simpa only using
        sum_tangentSplitRequestWeight_mul_sub
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (fun edge : V × V => flow edge.1 edge.2)
          (fun q => (q.factorization p : Real))
    _ = ∑ v : V, residual v * (label v).factorization p :=
      tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
        flow label residual hflow hdivergence p

/-! ## Weighted per-label port control -/

/-- With injective labels, the incident ledger at `label v` has exactly the
single contribution from `v`. -/
theorem tangentDistributedLabelIncidentLedger_at_label
    {V : Type*} [Fintype V]
    {label : V -> Nat} {residual portLoad : V -> Real}
    (hlabel : Function.Injective label) (v : V) :
    tangentDistributedLabelIncidentLedger label residual portLoad
        (label v) =
      |residual v| + 2 * portLoad v := by
  classical
  unfold tangentDistributedLabelIncidentLedger
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _hw hwv
    have hwLabel : label w ≠ label v := by
      intro hwLabel
      exact hwv (hlabel hwLabel)
    simp [hwLabel]
  · simp

/-- Pointwise weighted residual and port bounds control the weighted label
ledger. -/
theorem tangentDistributedLabelIncidentLedger_mul_le
    {V : Type*} [Fintype V]
    {label : V -> Nat} {residual portLoad : V -> Real}
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    (v : V) :
    (label v : Real) *
        tangentDistributedLabelIncidentLedger label residual portLoad
          (label v) <=
      weightedResidual + 2 * weightedPort := by
  rw [tangentDistributedLabelIncidentLedger_at_label hlabel v]
  calc
    (label v : Real) * (|residual v| + 2 * portLoad v) =
        (label v : Real) * |residual v| +
          2 * ((label v : Real) * portLoad v) := by ring
    _ <= weightedResidual + 2 * weightedPort := by
      exact add_le_add (hresidual v)
        (mul_le_mul_of_nonneg_left (hport v) (by norm_num))



/-- Injective labels promote the vertexwise incident estimate to every natural
label. -/
theorem tangentDistributedIncidentTraffic_le_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat)
    (residual portLoad : V -> Real)
    (hincident : forall v,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (fun edge : V × V => flow edge.1 edge.2) (label v) <=
        |residual v| + 2 * portLoad v)
    (hlabel : Function.Injective label) (q : Nat) :
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => flow edge.1 edge.2) q <=
      tangentDistributedLabelIncidentLedger label residual portLoad q := by
  classical
  by_cases hq : ∃ v : V, label v = q
  · obtain ⟨v, rfl⟩ := hq
    rw [tangentDistributedLabelIncidentLedger_at_label hlabel v]
    exact hincident v
  · have hnone : forall v : V, label v ≠ q := by
      intro v hv
      exact hq ⟨v, hv⟩
    have hzero :
        tangentIncidentFlowMass
            (tangentPositiveFlowEdges flow)
            (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
            (fun edge : V × V => flow edge.1 edge.2) q = 0 := by
      unfold tangentIncidentFlowMass tangentIncidentEdges
      apply Finset.sum_eq_zero
      intro edge hedge
      have hdata := Finset.mem_filter.mp hedge
      rcases hdata.2 with hsource | htarget
      · exact (hnone edge.1 hsource).elim
      · exact (hnone edge.2 htarget).elim
    rw [hzero]
    simp [tangentDistributedLabelIncidentLedger, hnone]

/-! ## Total and endpoint request counts -/





/-- Weighted pointwise residual and port estimates bound the normalized label
census ledger. -/
theorem tangentDistributedWeightedLabelCensusUpper_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (label : V -> Nat) (residual portLoad : V -> Real)
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    {labelUpper : Nat} (hlabelUpper : forall v, label v <= labelUpper)
    {L sigma : Real} (hL : 0 < L) (hsigma : 0 < sigma)
    (v : V) :
    (label v : Real) *
        tangentSplitCensusLabelRequestUpper L sigma
          (tangentDistributedLabelIncidentLedger label residual portLoad)
          (tangentDistributedSupportCount V) (label v) <=
      (4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
        (labelUpper : Real) * tangentDistributedSupportCount V := by
  have hweighted := tangentDistributedLabelIncidentLedger_mul_le
    hlabel hresidual hport v
  have hA : 0 <= 4 * L / sigma := by positivity
  calc
    (label v : Real) *
        tangentSplitCensusLabelRequestUpper L sigma
          (tangentDistributedLabelIncidentLedger label residual portLoad)
          (tangentDistributedSupportCount V) (label v) =
      (4 * L / sigma) *
          ((label v : Real) *
            tangentDistributedLabelIncidentLedger label residual portLoad
              (label v)) +
        (label v : Real) * tangentDistributedSupportCount V := by
      unfold tangentSplitCensusLabelRequestUpper
      ring
    _ <= (4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
        (labelUpper : Real) * tangentDistributedSupportCount V := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hweighted hA)
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast hlabelUpper v)
          (Nat.cast_nonneg _))



/-! ## Paper-parameter closure of the collision guard

The three budgets below mirror the actual parameter order in Section 9.
The main term is made small by the fixed band width `w`; the error and
ceiling terms are absorbed only after the mesh is fixed and `n` tends to
infinity.  None of them is a traffic or request-count hypothesis. -/







/-- Literal cancellation of `L * N = n` in the total- and incident-ledger
bounds.  This is the arithmetic step which prevents the final
`4*T+I_s+I_t` target from reappearing as an assembly premise. -/
theorem tangentDistributedResidualCollisionUpper_le_paperBudgets
    {V : Type*} [Fintype V]
    (residual : V -> Real) (cutTraffic weightedResidual weightedPort : Real)
    {n labelUpper : Nat} {L sigma N : Real}
    {trafficConstant incidentConstant tangentConstant width : Real}
    {trafficError incidentError : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hscale : L * N = (n : Real))
    (htotal : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hincident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N) :
    tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort <=
      tangentDistributedPaperMainBudget trafficConstant incidentConstant
          tangentConstant width sigma +
        tangentDistributedPaperErrorBudget trafficError incidentError sigma +
        tangentDistributedPaperCeilingBudget n labelUpper
          (tangentDistributedSupportCount V) := by
  unfold tangentDistributedResidualCollisionUpper
  unfold tangentSplitCensusTotalRequestUpper
    tangentDistributedPaperMainBudget
    tangentDistributedPaperErrorBudget
    tangentDistributedPaperCeilingBudget
  calc
    4 *
          (((4 * L / sigma) *
                tangentDistributedTotalTrafficLedger residual cutTraffic +
              tangentDistributedSupportCount V) /
            (n : Real)) +
        2 *
          (((4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
              (labelUpper : Real) * tangentDistributedSupportCount V) /
            (n : Real)) <=
      4 *
          (((4 * L / sigma) *
                (trafficConstant * tangentConstant * N * width +
                  trafficError * N) +
              tangentDistributedSupportCount V) /
            (n : Real)) +
        2 *
          (((4 * L / sigma) *
                (incidentConstant * tangentConstant * N * width +
                  incidentError * N) +
              (labelUpper : Real) * tangentDistributedSupportCount V) /
            (n : Real)) := by
      gcongr
    _ =
      ((16 * trafficConstant + 8 * incidentConstant) *
            tangentConstant * width) /
          sigma +
        (16 * trafficError + 8 * incidentError) / sigma +
        (4 + 2 * (labelUpper : Real)) *
            tangentDistributedSupportCount V /
          n := by
      rw [← hscale]
      field_simp [ne_of_gt hL, ne_of_gt hN, ne_of_gt hsigma]; ring

/-- Separate main, error, and ceiling smallness bounds imply the final
distributed residual-collision bound. -/
theorem tangentDistributedResidualCollisionUpper_le_of_paperSmallness
    {V : Type*} [Fintype V]
    (residual : V -> Real) (cutTraffic weightedResidual weightedPort : Real)
    {n labelUpper : Nat} {L sigma N density : Real}
    {trafficConstant incidentConstant tangentConstant width : Real}
    {trafficError incidentError : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hscale : L * N = (n : Real))
    (htotal : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hincident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma <=
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma <= density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n labelUpper
        (tangentDistributedSupportCount V) <= density ^ 2 / 96) :
    tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort <=
      density ^ 2 / 24 := by
  calc
    tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort <=
      tangentDistributedPaperMainBudget trafficConstant incidentConstant
          tangentConstant width sigma +
        tangentDistributedPaperErrorBudget trafficError incidentError sigma +
        tangentDistributedPaperCeilingBudget n labelUpper
          (tangentDistributedSupportCount V) :=
      tangentDistributedResidualCollisionUpper_le_paperBudgets
        residual cutTraffic weightedResidual weightedPort hL hsigma hN hscale
        htotal hincident
    _ <= density ^ 2 / 24 := by linarith

/-- The paper-scale budgets imply the exact per-request census inequality
consumed by the collision theorem. -/
theorem tangentDistributedRequest_census_small_of_paperBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat)
    (residual portLoad : V -> Real) (cutTraffic : Real)
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    {n labelUpper : Nat} (hlabelUpper : forall v, label v <= labelUpper)
    {L sigma N density : Real}
    {trafficConstant incidentConstant tangentConstant width : Real}
    {trafficError incidentError : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hscale : L * N = (n : Real))
    (htotal : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hweightedIncident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma <=
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma <= density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n labelUpper
        (tangentDistributedSupportCount V) <= density ^ 2 / 96)
    (request : TangentSplitRequest
      (tangentPositiveFlowEdges flow) L sigma
        (fun edge : V × V => flow edge.1 edge.2)) :
    4 * (tangentSplitCensusTotalRequestUpper L sigma
          (tangentDistributedTotalTrafficLedger residual cutTraffic)
          (tangentDistributedSupportCount V) / n) +
        (((tangentSplitRequestSource (P := Nat)
              (tangentStarEdgeSource label) request : Nat) : Real) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentDistributedLabelIncidentLedger label residual portLoad)
            (tangentDistributedSupportCount V)
            (tangentSplitRequestSource (tangentStarEdgeSource label)
              request) / n) +
        (((tangentSplitRequestTarget (P := Nat)
              (tangentStarEdgeTarget label) request : Nat) : Real) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentDistributedLabelIncidentLedger label residual portLoad)
            (tangentDistributedSupportCount V)
            (tangentSplitRequestTarget (tangentStarEdgeTarget label)
              request) / n) <= density ^ 2 / 24 := by
  let sourceVertex : V := request.1.1.1
  let targetVertex : V := request.1.1.2
  have hsourceLabel :
      tangentSplitRequestSource (tangentStarEdgeSource label) request =
        label sourceVertex := by rfl
  have htargetLabel :
      tangentSplitRequestTarget (tangentStarEdgeTarget label) request =
        label targetVertex := by rfl
  have hsource := tangentDistributedWeightedLabelCensusUpper_le
    label residual portLoad hlabel hresidual hport hlabelUpper
      hL hsigma sourceVertex
  have htarget := tangentDistributedWeightedLabelCensusUpper_le
    label residual portLoad hlabel hresidual hport hlabelUpper
      hL hsigma targetVertex
  rw [hsourceLabel, htargetLabel]
  have hn : 0 <= (n : Real) := Nat.cast_nonneg n
  have hsourceDiv := div_le_div_of_nonneg_right hsource hn
  have htargetDiv := div_le_div_of_nonneg_right htarget hn
  calc
    4 * (tangentSplitCensusTotalRequestUpper L sigma
          (tangentDistributedTotalTrafficLedger residual cutTraffic)
          (tangentDistributedSupportCount V) / n) +
        ((label sourceVertex : Real) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentDistributedLabelIncidentLedger label residual portLoad)
            (tangentDistributedSupportCount V) (label sourceVertex) / n) +
        ((label targetVertex : Real) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentDistributedLabelIncidentLedger label residual portLoad)
            (tangentDistributedSupportCount V) (label targetVertex) / n) <=
      tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort := by
      unfold tangentDistributedResidualCollisionUpper
      linarith
    _ <= density ^ 2 / 24 :=
      tangentDistributedResidualCollisionUpper_le_of_paperSmallness
        residual cutTraffic weightedResidual weightedPort hL hsigma hN hscale
        htotal hweightedIncident hmain herror hceiling

/-- The paper-scale distributed bounds close the normalized collision census
at `1/8`. -/
theorem tangentDistributedCollisionCensusBudget_le_eighth_of_paperBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat)
    (residual portLoad : V -> Real) (cutTraffic : Real)
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    {n labelUpper : Nat} (hlabelUpper : forall v, label v <= labelUpper)
    {L sigma N density : Real}
    {trafficConstant incidentConstant tangentConstant width : Real}
    {trafficError incidentError : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hdensity : 0 < density) (hscale : L * N = (n : Real))
    (htotal : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hweightedIncident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma <=
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma <= density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n labelUpper
        (tangentDistributedSupportCount V) <= density ^ 2 / 96)
    (request : TangentSplitRequest
      (tangentPositiveFlowEdges flow) L sigma
        (fun edge : V × V => flow edge.1 edge.2)) :
    tangentSplitNormalizedCollisionCensusBudget
        (flow := fun edge : V × V => flow edge.1 edge.2)
        n (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        L sigma
        (tangentDistributedTotalTrafficLedger residual cutTraffic)
        (tangentDistributedLabelIncidentLedger label residual portLoad)
        (tangentDistributedSupportCount V)
        (tangentDensityDisjointCoefficient density)
        (tangentDensitySharedCoefficient density) request <= 1 / 8 := by
  exact tangentSplitNormalizedCollisionCensusBudget_le_eighth_of_density
    n (tangentPositiveFlowEdges flow)
      (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
      L sigma (tangentDistributedTotalTrafficLedger residual cutTraffic)
      (tangentDistributedLabelIncidentLedger label residual portLoad)
      (tangentDistributedSupportCount V) density hdensity request
      (tangentDistributedRequest_census_small_of_paperBounds
        flow label residual portLoad cutTraffic hlabel hresidual hport
        hlabelUpper hL hsigma hN hscale htotal hweightedIncident
        hmain herror hceiling request)

/-! ## Connector to the actual paper collision terminal -/

namespace BankPaperRealization

/-- Star-free connector from a distributed residual earthmover to the
actual paper split-request terminal.  Its earthmover-side quantitative
inputs are the literal residual/cut/port ledgers; the clean-list lower-card
and effective-density estimates and the paper's fixed main/error/ceiling
parameter budgets also remain explicit.  There is no request-wise or
aggregate final collision premise. -/
theorem tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : Real} {depth n M : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset Nat)
    (K h Phead X0 : Nat)
    (label : V -> Nat) (residual portLoad : V -> Real)
    (cutTraffic : Real) (vertexFlow : V -> V -> Real)
    (hflowNonneg : forall source target,
      0 <= vertexFlow source target)
    (hdivergence : forall v,
      tangentFlowDivergence vertexFlow v = residual v)
    (hpositiveEndpoints : forall {source target},
      0 < vertexFlow source target -> source ≠ target)
    (htrafficFull : tangentFlowTraffic vertexFlow <=
      tangentDistributedTotalTrafficLedger residual cutTraffic)
    (hincidentVertex : forall v,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges vertexFlow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (fun edge : V × V => vertexFlow edge.1 edge.2) (label v) <=
        |residual v| + 2 * portLoad v)
    (hlabelInjective : Function.Injective label)
    (hlabelPrime : forall v, (label v).Prime)
    (weightedResidual weightedPort : Real)
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    (labelUpper : Nat) (density : Real)
    (hn : 0 < n) (hdensity : 0 < density)
    (hlabelUpper : forall v, label v <= labelUpper)
    (hlabelUpperLe : (labelUpper : Real) <= n)
    (hlabelUpperSq : (labelUpper : Real) ^ 2 <= n)
    {L sigma N : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hscale : L * N = (n : Real))
    (trafficConstant incidentConstant tangentConstant width : Real)
    (trafficError incidentError : Real)
    (htotal : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hweightedIncident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma <=
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma <= density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n labelUpper
        (tangentDistributedSupportCount V) <= density ^ 2 / 96)
    (lowerCard : TangentSplitRequest
      (tangentPositiveFlowEdges vertexFlow) L sigma
        (fun edge : V × V => vertexFlow edge.1 edge.2) -> Nat)
    (hlowerPos : forall request, 0 < lowerCard request)
    (hlower : forall request,
      lowerCard request <=
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges vertexFlow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (fun edge : V × V => vertexFlow edge.1 edge.2)
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : forall request side,
      density * n <= (lowerCard request : Real) *
        tangentEndpointLabel
          (tangentSplitRequestSource (tangentStarEdgeSource label))
          (tangentSplitRequestTarget (tangentStarEdgeTarget label))
          side request) :
    (forall v, tangentFlowDivergence vertexFlow v = residual v) ∧
      (forall p,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges vertexFlow) L sigma
                (fun edge : V × V => vertexFlow edge.1 edge.2),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource (tangentStarEdgeSource label)
                    request).factorization p : Real) -
                ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                    request).factorization p : Real))) =
          ∑ v : V, residual v * (label v).factorization p) ∧
      ∃ multiplier : TangentSplitRequest
          (tangentPositiveFlowEdges vertexFlow) L sigma
            (fun edge : V × V => vertexFlow edge.1 edge.2) -> Nat,
        (forall request,
          multiplier request ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges vertexFlow)
              (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
              L sigma (fun edge : V × V => vertexFlow edge.1 edge.2)
              n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request) ∧
        TangentEndpointsDistinct
          (tangentSplitRequests
            (tangentPositiveFlowEdges vertexFlow) L sigma
              (fun edge : V × V => vertexFlow edge.1 edge.2))
          (tangentSplitRequestSource (tangentStarEdgeSource label))
          (tangentSplitRequestTarget (tangentStarEdgeTarget label))
          multiplier := by
  let edges := tangentPositiveFlowEdges vertexFlow
  let source := tangentStarEdgeSource label
  let target := tangentStarEdgeTarget label
  let flow : V × V -> Real :=
    fun edge => vertexFlow edge.1 edge.2
  have hsourceTarget : ∀ edge ∈ edges,
      source edge ≠ target edge := by
    intro edge hedge
    exact tangentDistributedPositiveEdge_labels_ne
      vertexFlow hpositiveEndpoints hlabelInjective hedge
  have hflow : ∀ edge ∈ edges, 0 <= flow edge := by
    intro edge _hedge
    exact hflowNonneg edge.1 edge.2
  have hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime := by
    intro edge _hedge
    exact ⟨hlabelPrime edge.1, hlabelPrime edge.2⟩
  have hrequestDistinct : forall request :
      TangentSplitRequest edges L sigma flow,
      tangentSplitRequestSource source request ≠
        tangentSplitRequestTarget target request := by
    intro request
    simpa only [tangentSplitRequestSource, tangentSplitRequestTarget,
      tangentSplitRequestEdge] using
        hsourceTarget request.1.1 request.1.2
  have hrequestPrime : forall request :
      TangentSplitRequest edges L sigma flow,
      forall side : TangentEndpointSide,
        (tangentEndpointLabel
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) side request).Prime := by
    intro request side
    have hp := hprime request.1.1 request.1.2
    cases side with
    | source =>
        simpa only [tangentEndpointLabel] using hp.1
    | target =>
        simpa only [tangentEndpointLabel] using hp.2
  have hrequestUpper : forall request :
      TangentSplitRequest edges L sigma flow,
      forall side : TangentEndpointSide,
        tangentEndpointLabel
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) side request <= labelUpper := by
    intro request side
    cases side with
    | source =>
        simpa only [tangentEndpointLabel, tangentSplitRequestSource,
          tangentSplitRequestEdge, source, tangentStarEdgeSource] using
            hlabelUpper request.1.1.1
    | target =>
        simpa only [tangentEndpointLabel, tangentSplitRequestTarget,
          tangentSplitRequestEdge, target, tangentStarEdgeTarget] using
            hlabelUpper request.1.1.2
  have hpairArithmetic : forall leftRequest rightRequest,
      forall _hne : leftRequest ≠ rightRequest,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          leftRequest rightRequest : Real) /
          (lowerCard leftRequest * lowerCard rightRequest) <=
        tangentDensityDisjointCoefficient density / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source leftRequest) rightRequest
            then tangentDensitySharedCoefficient density *
                tangentSplitRequestSource source leftRequest / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target leftRequest) rightRequest
            then tangentDensitySharedCoefficient density *
                tangentSplitRequestTarget target leftRequest / n
            else 0) := by
    intro leftRequest rightRequest _hne
    exact tangentOrderedPairEndpointBudget_div_le_densityCoefficients
      n K h labelUpper (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) lowerCard density hn hdensity
        hlowerPos hrequestDistinct hrequestPrime hrequestUpper
        hlabelUpperLe hlabelUpperSq hlowerScale leftRequest rightRequest
  have htraffic : (∑ edge ∈ edges, flow edge) <=
      tangentDistributedTotalTrafficLedger residual cutTraffic := by
    exact sum_tangentDistributedPositiveEdges_le_trafficLedger
      vertexFlow residual cutTraffic hflowNonneg htrafficFull
  have hincident : forall q,
      tangentIncidentFlowMass edges source target flow q <=
        tangentDistributedLabelIncidentLedger label residual portLoad q := by
    intro q
    exact tangentDistributedIncidentTraffic_le_ledger
      vertexFlow label residual portLoad hincidentVertex hlabelInjective q
  have hsupport : edges.card <= tangentDistributedSupportCount V :=
    card_tangentPositiveFlowEdges_le_distributedSupportCount vertexFlow
  have hbudget : forall request : TangentSplitRequest edges L sigma flow,
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          (tangentDistributedTotalTrafficLedger residual cutTraffic)
          (tangentDistributedLabelIncidentLedger label residual portLoad)
          (tangentDistributedSupportCount V)
          (tangentDensityDisjointCoefficient density)
          (tangentDensitySharedCoefficient density) request <= 1 / 8 := by
    intro request
    exact tangentDistributedCollisionCensusBudget_le_eighth_of_paperBounds
      vertexFlow label residual portLoad cutTraffic hlabelInjective
      hresidual hport hlabelUpper hL hsigma hN hdensity hscale
      htotal hweightedIncident hmain herror hceiling request
  exact ⟨hdivergence,
    tangentDistributedSplitRequest_factorizationBoundary_eq_residual
      vertexFlow label residual hflowNonneg hdivergence L sigma,
    R.tangentPaperSplitEndpointsDistinct_of_normalizedCensusBudget
      certificate fixedExceptional K h Phead X0 edges source target flow
      hsourceTarget lowerCard hlowerPos hlower hprime
      (tangentDistributedTotalTrafficLedger residual cutTraffic)
      (tangentDistributedLabelIncidentLedger label residual portLoad)
      (tangentDistributedSupportCount V)
      (tangentDensityDisjointCoefficient density)
      (tangentDensitySharedCoefficient density)
      (tangentDensityDisjointCoefficient_nonneg hdensity.le)
      (tangentDensitySharedCoefficient_nonneg hdensity.le)
      hpairArithmetic hflow hL hsigma htraffic hincident hsupport hbudget⟩

end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal008_001.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus
