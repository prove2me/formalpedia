-- Prove2me | solution 1 for MarkovChainCLT.ergodicWithRate_of_geoDriftCondition
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:10:45.926878+00:00
-- url     : https://prove2.me/submissions/b7e6291f-1ec1-4b3b-ad7b-cb0815628d55

import Definitions.Def_MarkovErgodicity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_MarkovDriftMinorization
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_MarkovChainCLT_integrable_of_geoDriftCondition
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.NNRealPreprocessor
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/- Complete direct-block proof of geometric total-variation convergence
from geometric drift, multi-step smallness, and Harris convergence.
Four complete elementary lemmas are retained from earlier verified sources
with precise attribution in the component bodies. The selected-event DCT
argument adapts the earlier HarrisAlpha proof as credited below.
All seven component bodies are included in full. Only registered public
theorems 205b10ed and 809417df are imported; no hidden helper is imported. -/

section GeometricRateComponent1

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

set_option maxHeartbeats 2000000

namespace MixtureTVConvergence

variable {X : Type*} [MeasurableSpace X]

-- The selected-event and DCT argument adapts Round34 HarrisAlpha.lean, authored
-- by bounded_resume, SHA256 856652424e88d9e12698f1621c0b623caffb73ec5d1e85f8dd0df31238f93270.
-- Its complete source is retained in provenance; no path-law helper is imported.

theorem abs_measure_sub_le_one (mu nu : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (A : Set X) :
    |(mu A).toReal - (nu A).toReal| <= 1 := by
  have hmu0 : 0 <= (mu A).toReal := ENNReal.toReal_nonneg
  have hnu0 : 0 <= (nu A).toReal := ENNReal.toReal_nonneg
  have hmu1 : (mu A).toReal <= 1 := by
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using (prob_le_one (μ := mu) (s := A))
  have hnu1 : (nu A).toReal <= 1 := by
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using (prob_le_one (μ := nu) (s := A))
  rw [abs_le]
  constructor <;> linarith

theorem tv_nonneg (mu nu : Measure X) : 0 <= tvDist mu nu := by
  apply Real.sSup_nonneg
  rintro r ⟨A, _hA, rfl⟩
  exact abs_nonneg _

theorem tv_values_bddAbove (mu nu : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    BddAbove {r : Real | ∃ A : Set X, MeasurableSet A ∧
      r = |(mu A).toReal - (nu A).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, _hA, rfl⟩
  exact abs_measure_sub_le_one mu nu A

theorem event_le_tv (mu nu : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {A : Set X} (hA : MeasurableSet A) :
    |(mu A).toReal - (nu A).toReal| <= tvDist mu nu :=
  le_csSup (tv_values_bddAbove mu nu) ⟨A, hA, rfl⟩

noncomputable def eventDeviation (P : Kernel X X) [IsMarkovKernel P]
    (pi : Measure X) (n : Nat) (A : Set X) (x : X) : Real :=
  |((iterKernel P n x) A).toReal - (pi A).toReal|

theorem eventDeviation_measurable (P : Kernel X X) [IsMarkovKernel P]
    (pi : Measure X) (n : Nat) {A : Set X} (hA : MeasurableSet A) :
    Measurable (eventDeviation P pi n A) :=
  ((Kernel.measurable_coe _ hA).ennreal_toReal.sub_const _).abs

theorem eventDeviation_nonneg (P : Kernel X X) [IsMarkovKernel P]
    (pi : Measure X) (n : Nat) (A : Set X) (x : X) :
    0 <= eventDeviation P pi n A x := abs_nonneg _

theorem eventDeviation_le_one (P : Kernel X X) [IsMarkovKernel P]
    (pi : Measure X) [IsProbabilityMeasure pi] (n : Nat) (A : Set X) (x : X) :
    eventDeviation P pi n A x <= 1 :=
  abs_measure_sub_le_one (iterKernel P n x) pi A

theorem eventDeviation_le_tv (P : Kernel X X) [IsMarkovKernel P]
    (pi : Measure X) [IsProbabilityMeasure pi] (n : Nat)
    {A : Set X} (hA : MeasurableSet A) (x : X) :
    eventDeviation P pi n A x <= tvDist (iterKernel P n x) pi :=
  event_le_tv (iterKernel P n x) pi hA

theorem bind_real (K : Kernel X X) [IsMarkovKernel K]
    (nu : Measure X) [IsProbabilityMeasure nu] {A : Set X} (hA : MeasurableSet A) :
    ((K ∘ₘ nu) A).toReal = ∫ x, (K x A).toReal ∂nu := by
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  refine (integral_toReal (Kernel.measurable_coe _ hA).aemeasurable ?_).symm
  filter_upwards with x
  exact measure_lt_top _ _

theorem mixture_event_bound (P : Kernel X X) [IsMarkovKernel P]
    (pi nu : Measure X) [IsProbabilityMeasure pi] [IsProbabilityMeasure nu]
    (n : Nat) {A : Set X} (hA : MeasurableSet A) :
    |(((iterKernel P n) ∘ₘ nu) A).toReal - (pi A).toReal| <=
      ∫ x, eventDeviation P pi n A x ∂nu := by
  have hFint : Integrable (fun x => ((iterKernel P n x) A).toReal) nu := by
    apply Integrable.of_bound (Kernel.measurable_coe _ hA).ennreal_toReal.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using (prob_le_one (μ := iterKernel P n x) (s := A))
  have hcent : (∫ x, ((iterKernel P n x) A).toReal ∂nu) - (pi A).toReal =
      ∫ x, ((iterKernel P n x) A).toReal - (pi A).toReal ∂nu := by
    rw [integral_sub hFint (integrable_const _), integral_const]
    simp
  rw [bind_real _ nu hA, hcent]
  exact abs_integral_le_integral_abs

theorem tendsto_tvDist_comp_of_pointwise (P : Kernel X X) [IsMarkovKernel P]
    (pi nu : Measure X) [IsProbabilityMeasure pi] [IsProbabilityMeasure nu]
    (hconv : ∀ x, Tendsto (fun n => tvDist (iterKernel P n x) pi) atTop (nhds 0)) :
    Tendsto (fun n => tvDist ((iterKernel P n) ∘ₘ nu) pi) atTop (nhds 0) := by
  classical
  let a := fun n => tvDist ((iterKernel P n) ∘ₘ nu) pi
  have hnear : ∀ n : Nat, ∃ A : Set X, MeasurableSet A ∧
      a n <= (∫ x, eventDeviation P pi n A x ∂nu) + 1 / ((n : Real) + 1) := by
    intro n
    have heps : 0 < 1 / ((n : Real) + 1) := by positivity
    have hs : {r : Real | ∃ A : Set X, MeasurableSet A ∧
        r = |(((iterKernel P n) ∘ₘ nu) A).toReal - (pi A).toReal|}.Nonempty :=
      ⟨0, ∅, by simp, by simp⟩
    obtain ⟨r, ⟨A, hA, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hs
      (show a n - 1 / ((n : Real) + 1) < a n by linarith)
    have hb := mixture_event_bound P pi nu n hA
    exact ⟨A, hA, by linarith⟩
  choose A hA hnear using hnear
  have hpoint : ∀ x, Tendsto (fun n => eventDeviation P pi n (A n) x)
      atTop (nhds 0) := by
    intro x
    exact squeeze_zero (fun n => eventDeviation_nonneg P pi n (A n) x)
      (fun n => eventDeviation_le_tv P pi n (hA n) x) (hconv x)
  have hint : Tendsto (fun n => ∫ x, eventDeviation P pi n (A n) x ∂nu)
      atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := nu)
      (fun _x : X => (1 : Real))
      (fun n => (eventDeviation_measurable P pi n (hA n)).aestronglyMeasurable)
      (integrable_const 1)
      (fun n => ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (eventDeviation_nonneg P pi n (A n) x)]
        exact eventDeviation_le_one P pi n (A n) x))
      (ae_of_all _ hpoint)
    simpa using h
  have herr : Tendsto (fun n : Nat => 1 / ((n : Real) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact squeeze_zero (fun n => tv_nonneg ((iterKernel P n) ∘ₘ nu) pi)
    hnear (by simpa using hint.add herr)

theorem tendsto_tvDist_comp (P : Kernel X X) [IsMarkovKernel P]
    (pi nu : Measure X) [IsProbabilityMeasure pi] [IsProbabilityMeasure nu]
    (hP : HarrisErgodic P pi) :
    Tendsto (fun n => tvDist ((iterKernel P n) ∘ₘ nu) pi) atTop (nhds 0) :=
  tendsto_tvDist_comp_of_pointwise P pi nu hP.2

end MixtureTVConvergence

end GeometricRateComponent1

section GeometricRateComponent2

open Filter Finset MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace GeoDriftBlock

set_option maxHeartbeats 2000000

variable {X : Type*} [MeasurableSpace X]

/- The next two complete lemmas retain the proofs in Round35
DyadicResolvent.lean lines 103-111, SHA256
21152c0c3895a1f2d1f2425845643b7a6be1ddd986373e3ee8a35bad3da06d8b.
Only their surrounding namespace is changed. -/
theorem iterKernel_eq_pow (P : Kernel X X) (n : ℕ) : iterKernel P n = P ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterKernel_succ, ih] using (pow_succ' P n).symm

theorem iterKernel_comp (P : Kernel X X) (n m : ℕ) :
    iterKernel P n ∘ₖ iterKernel P m = iterKernel P (n + m) := by
  simp only [iterKernel_eq_pow]
  exact (Kernel.pow_add P n m).symm

/- This complete lemma retains Round35 ResolventBounds.lean lines 16-50,
SHA256 d7dd3e0e17f63a6ee330e5469c2ff05163db3a4335a7304950abf4026730df8e.
Only its surrounding namespace is changed. -/
theorem iter_integrable_growth (P : Kernel X X) [IsMarkovKernel P]
    (U : X → ℝ) (hUm : Measurable U) (hU0 : ∀ x, 0 ≤ U x)
    (hUi : ∀ x, Integrable U (P x)) (B : ℝ)
    (hgrowth : ∀ x, (∫ y, U y ∂P x) ≤ U x + B) (n : ℕ) (x : X) :
    Integrable U (iterKernel P n x) ∧
      (∫ y, U y ∂iterKernel P n x) ≤ U x + n * B := by
  induction n with
  | zero =>
      simp only [iterKernel_zero, Kernel.id_apply, Nat.cast_zero, zero_mul, add_zero]
      exact ⟨integrable_dirac' hUm.stronglyMeasurable (by simp),
        le_of_eq (integral_dirac' U x hUm.stronglyMeasurable)⟩
  | succ n ih =>
      have hnorm : (fun y => ‖U y‖) = U := by
        funext y
        exact Real.norm_of_nonneg (hU0 y)
      have hPi : Integrable (fun y => ∫ z, U z ∂P y) (iterKernel P n x) := by
        apply (ih.1.add (integrable_const B)).mono'
          hUm.stronglyMeasurable.integral_kernel.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (integral_nonneg hU0)]
          exact hgrowth y
      have hi : Integrable U ((P ∘ₖ iterKernel P n) x) := by
        apply (integrable_comp_iff hUm.aestronglyMeasurable).mpr
        refine ⟨Filter.Eventually.of_forall hUi, ?_⟩
        simpa only [hnorm] using hPi
      refine ⟨hi, ?_⟩
      rw [iterKernel_succ, Kernel.integral_comp hi]
      calc
        (∫ y, ∫ z, U z ∂P y ∂iterKernel P n x) ≤
            ∫ y, U y + B ∂iterKernel P n x :=
          integral_mono hPi (ih.1.add (integrable_const B)) hgrowth
        _ = (∫ y, U y ∂iterKernel P n x) + B := by
          rw [integral_add ih.1 (integrable_const B)]
          simp
        _ ≤ U x + (n + 1 : ℕ) * B := by push_cast; linarith [ih.2]

theorem normalize_drift (P : Kernel X X) [IsMarkovKernel P]
    (V : X → ℝ) (hV1 : ∀ x, 1 ≤ V x) (C : Set X)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C) :
    ∃ a B : ℝ, 0 < a ∧ a < 1 ∧ 1 ≤ B ∧
      ∀ x, (∫ y, V y ∂P x) ≤ a * V x + B * C.indicator (fun _ => 1) x := by
  let d0 : ℝ := min d (1 / 2)
  have hd0 : 0 < d0 := lt_min hd (by norm_num)
  have hd0d : d0 ≤ d := min_le_left _ _
  have hd0half : d0 ≤ 1 / 2 := min_le_right _ _
  refine ⟨1 - d0, max b 1, by linarith, by linarith, le_max_right _ _, ?_⟩
  intro x
  have hV0 : 0 ≤ V x := le_trans zero_le_one (hV1 x)
  have hm := mul_le_mul_of_nonneg_right hd0d hV0
  have hb := le_max_left b (1 : ℝ)
  have h := hdrift.2 x
  by_cases hx : x ∈ C
  · simp only [Set.indicator_of_mem hx, mul_one] at h ⊢
    nlinarith
  · simp only [Set.indicator_of_notMem hx, mul_zero] at h ⊢
    nlinarith

theorem growth_of_normalized (P : Kernel X X) [IsMarkovKernel P]
    (V : X → ℝ) (hV0 : ∀ x, 0 ≤ V x) (C : Set X)
    (a B : ℝ) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hdrift : ∀ x, (∫ y, V y ∂P x) ≤ a * V x + B * C.indicator (fun _ => 1) x) :
    ∀ x, (∫ y, V y ∂P x) ≤ V x + B := by
  intro x
  have hmul : a * V x ≤ V x := by
    simpa using mul_le_mul_of_nonneg_right ha1 (hV0 x)
  have hC : B * C.indicator (fun _ => (1 : ℝ)) x ≤ B := by
    by_cases hx : x ∈ C <;> simp [hx, hB]
  linarith [hdrift x]

theorem iter_integrable (P : Kernel X X) [IsMarkovKernel P]
    (V : X → ℝ) (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (hVi : ∀ x, Integrable V (P x)) (C : Set X)
    (a B : ℝ) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hdrift : ∀ x, (∫ y, V y ∂P x) ≤ a * V x + B * C.indicator (fun _ => 1) x)
    (n : ℕ) (x : X) : Integrable V (iterKernel P n x) :=
  (iter_integrable_growth P V hV hV0 hVi B
    (growth_of_normalized P V hV0 C a B ha1 hB hdrift) n x).1

theorem iter_global_bound (P : Kernel X X) [IsMarkovKernel P]
    (V : X → ℝ) (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (hVi : ∀ x, Integrable V (P x)) (C : Set X)
    (a B : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hB : 0 ≤ B)
    (hdrift : ∀ x, (∫ y, V y ∂P x) ≤ a * V x + B * C.indicator (fun _ => 1) x)
    (n : ℕ) (x : X) :
    (∫ y, V y ∂iterKernel P n x) ≤ a ^ n * V x + B / (1 - a) := by
  have hi := iter_integrable P V hV hV0 hVi C a B ha1.le hB hdrift
  have hglobal : ∀ y, (∫ z, V z ∂P y) ≤ a * V y + B := by
    intro y
    have hC : B * C.indicator (fun _ => (1 : ℝ)) y ≤ B := by
      by_cases hy : y ∈ C <;> simp [hy, hB]
    linarith [hdrift y]
  have hK : 0 ≤ B / (1 - a) := div_nonneg hB (by linarith)
  have hbalance : a * (B / (1 - a)) + B = B / (1 - a) := by
    field_simp [ne_of_gt (show 0 < 1 - a by linarith)]
    ring
  induction n with
  | zero =>
      simp only [iterKernel_zero, Kernel.id_apply, pow_zero, one_mul]
      rw [integral_dirac' V x hV.stronglyMeasurable]
      linarith
  | succ n ih =>
      have hPi : Integrable (fun y => ∫ z, V z ∂P y) (iterKernel P n x) :=
        (hi (n + 1) x).integral_comp
      rw [iterKernel_succ, Kernel.integral_comp (hi (n + 1) x)]
      calc
        (∫ y, ∫ z, V z ∂P y ∂iterKernel P n x) ≤
            ∫ y, a * V y + B ∂iterKernel P n x :=
          integral_mono hPi (((hi n x).const_mul a).add (integrable_const B)) hglobal
        _ = a * (∫ y, V y ∂iterKernel P n x) + B := by
          rw [integral_add ((hi n x).const_mul a) (integrable_const B), integral_const_mul]
          simp
        _ ≤ a * (a ^ n * V x + B / (1 - a)) + B := by gcongr
        _ = a ^ (n + 1) * V x + B / (1 - a) := by
          rw [pow_succ]
          nlinarith [hbalance]

theorem iter_occupation_bound (P : Kernel X X) [IsMarkovKernel P]
    (V : X → ℝ) (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (hVi : ∀ x, Integrable V (P x)) (C : Set X) (hC : MeasurableSet C)
    (a B : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hdrift : ∀ x, (∫ y, V y ∂P x) ≤ a * V x + B * C.indicator (fun _ => 1) x)
    (n : ℕ) (x : X) :
    (∫ y, V y ∂iterKernel P n x) ≤
      a ^ n * V x + B * ∑ i ∈ Finset.range n, (iterKernel P i x).real C := by
  have hi := iter_integrable P V hV hV0 hVi C a B ha1 hB hdrift
  induction n with
  | zero =>
      simp only [iterKernel_zero, Kernel.id_apply, pow_zero, one_mul,
        Finset.sum_range_zero, mul_zero, add_zero]
      exact le_of_eq (integral_dirac' V x hV.stronglyMeasurable)
  | succ n ih =>
      have hPi : Integrable (fun y => ∫ z, V z ∂P y) (iterKernel P n x) :=
        (hi (n + 1) x).integral_comp
      have hCi : Integrable (C.indicator (fun _ => (1 : ℝ))) (iterKernel P n x) :=
        (integrable_const 1).indicator hC
      have hsum : 0 ≤ ∑ i ∈ Finset.range n, (iterKernel P i x).real C :=
        Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
      have hscale : a * (B * ∑ i ∈ Finset.range n, (iterKernel P i x).real C) ≤
          B * ∑ i ∈ Finset.range n, (iterKernel P i x).real C := by
        simpa using mul_le_mul_of_nonneg_right ha1 (mul_nonneg hB hsum)
      rw [iterKernel_succ, Kernel.integral_comp (hi (n + 1) x)]
      calc
        (∫ y, ∫ z, V z ∂P y ∂iterKernel P n x) ≤
            ∫ y, a * V y + B * C.indicator (fun _ => 1) y ∂iterKernel P n x :=
          integral_mono hPi (((hi n x).const_mul a).add (hCi.const_mul B)) hdrift
        _ = a * (∫ y, V y ∂iterKernel P n x) + B * (iterKernel P n x).real C := by
          rw [integral_add ((hi n x).const_mul a) (hCi.const_mul B),
            integral_const_mul, integral_const_mul, integral_indicator hC]
          simp
        _ ≤ a * (a ^ n * V x + B * ∑ i ∈ Finset.range n, (iterKernel P i x).real C) +
            B * (iterKernel P n x).real C := by gcongr
        _ ≤ a ^ (n + 1) * V x + B * ∑ i ∈ Finset.range (n + 1),
            (iterKernel P i x).real C := by
          rw [Finset.sum_range_succ, pow_succ]
          nlinarith [hscale]

theorem finite_occupation (P : Kernel X X) [IsMarkovKernel P]
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVi : ∀ x, Integrable V (P x)) (C : Set X) (hC : MeasurableSet C)
    (a B : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hB : 0 < B)
    (hdrift : ∀ x, (∫ y, V y ∂P x) ≤ a * V x + B * C.indicator (fun _ => 1) x)
    (L : ℝ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ x, V x ≤ L →
      1 / (2 * B) ≤ ∑ i ∈ Finset.range T, (iterKernel P i x).real C := by
  have hV0 : ∀ x, 0 ≤ V x := fun x => le_trans zero_le_one (hV1 x)
  have hlim : Tendsto (fun n : ℕ => a ^ n * L) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const L
  obtain ⟨k, hk⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨k + 1, by omega, ?_⟩
  intro x hx
  have hi := iter_integrable P V hV hV0 hVi C a B ha1.le hB.le hdrift (k + 1) x
  have hlow : (1 : ℝ) ≤ ∫ y, V y ∂iterKernel P (k + 1) x := by
    simpa using integral_mono (integrable_const (1 : ℝ)) hi hV1
  have hupper := iter_occupation_bound P V hV hV0 hVi C hC a B ha0 ha1.le hB.le
    hdrift (k + 1) x
  have hpow : a ^ (k + 1) * V x ≤ a ^ (k + 1) * L :=
    mul_le_mul_of_nonneg_left hx (pow_nonneg ha0 _)
  have hsmall := hk (k + 1) (by omega)
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
  nlinarith

end GeoDriftBlock

end GeometricRateComponent2

section GeometricRateComponent3

open Filter Finset MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace GeoDriftBlock

set_option maxHeartbeats 3000000

variable {X : Type*} [MeasurableSpace X]

theorem prob_real_le_one (μ : Measure X) [IsProbabilityMeasure μ] (A : Set X) :
    μ.real A ≤ 1 := by
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  simpa using (prob_le_one (μ := μ) (s := A))

theorem kernel_event_integrable (Q : Kernel X X) [IsMarkovKernel Q]
    (μ : Measure X) [IsFiniteMeasure μ] {A : Set X} (hA : MeasurableSet A) :
    Integrable (fun y => (Q y).real A) μ := by
  apply Integrable.of_bound (Q.measurable_coe hA).ennreal_toReal.aestronglyMeasurable 1
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact prob_real_le_one (Q y) A

theorem comp_real_apply (Q P : Kernel X X) [IsMarkovKernel Q] [IsMarkovKernel P]
    (x : X) {A : Set X} (hA : MeasurableSet A) :
    ((Q ∘ₖ P) x).real A = ∫ y, (Q y).real A ∂P x := by
  change (((Q ∘ₖ P) x) A).toReal = _
  rw [Kernel.comp_apply]
  exact MixtureTVConvergence.bind_real Q (P x) hA

theorem propagated_minorization (P : Kernel X X) [IsMarkovKernel P]
    (C : Set X) (hC : MeasurableSet C) (m : ℕ)
    (ε : ℝ) (hε : 0 ≤ ε) (ν : Measure X) [IsProbabilityMeasure ν]
    (hminor : ∀ y ∈ C, ∀ A : Set X, MeasurableSet A →
      ENNReal.ofReal ε * ν A ≤ iterKernel P m y A)
    (i k : ℕ) (x : X) {A : Set X} (hA : MeasurableSet A) :
    ε * (iterKernel P i x).real C * ((iterKernel P k) ∘ₘ ν).real A ≤
      (iterKernel P (k + m + i) x).real A := by
  have hfuture : ∀ y ∈ C,
      ε * ((iterKernel P k) ∘ₘ ν).real A ≤ (iterKernel P (k + m) y).real A := by
    intro y hy
    have hle : ENNReal.ofReal ε • ν ≤ iterKernel P m y := by
      apply Measure.le_iff.mpr
      intro D hD
      simpa only [Measure.smul_apply, smul_eq_mul] using hminor y hy D hD
    have hmono := integral_mono_measure hle
      (ae_of_all _ fun z => ENNReal.toReal_nonneg :
        ∀ᵐ z ∂iterKernel P m y, 0 ≤ (iterKernel P k z).real A)
      (kernel_event_integrable (iterKernel P k) (iterKernel P m y) hA)
    rw [integral_smul_measure, ENNReal.toReal_ofReal hε] at hmono
    rw [← iterKernel_comp P k m, comp_real_apply _ _ y hA]
    simpa only [Measure.real, MixtureTVConvergence.bind_real _ _ hA, smul_eq_mul]
      using hmono
  have hpoint : ∀ y,
      C.indicator (fun _ => ε * ((iterKernel P k) ∘ₘ ν).real A) y ≤
        (iterKernel P (k + m) y).real A := by
    intro y
    by_cases hy : y ∈ C
    · simpa only [Set.indicator_of_mem hy] using hfuture y hy
    · simp only [Set.indicator_of_notMem hy]
      exact ENNReal.toReal_nonneg
  have hbound := integral_mono
    ((integrable_const (ε * ((iterKernel P k) ∘ₘ ν).real A)).indicator hC)
    (kernel_event_integrable (iterKernel P (k + m)) (iterKernel P i x) hA) hpoint
  rw [integral_indicator hC] at hbound
  rw [← iterKernel_comp P (k + m) i, comp_real_apply _ _ x hA]
  simpa only [setIntegral_const, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hbound

theorem tv_le_of_event_le (μ ν : Measure X) (r : ℝ)
    (hr : ∀ A : Set X, MeasurableSet A → |μ.real A - ν.real A| ≤ r) :
    tvDist μ ν ≤ r := by
  apply csSup_le
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  · rintro t ⟨A, hA, rfl⟩
    exact hr A hA

theorem averaged_minorization_lower (P : Kernel X X) [IsMarkovKernel P]
    (π ν : Measure X) [IsProbabilityMeasure π] [IsProbabilityMeasure ν]
    (C : Set X) (hC : MeasurableSet C) (m T N : ℕ) (hT : 1 ≤ T)
    (hN : m + T ≤ N) (ε B e : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hB : 0 < B) (he : 0 ≤ e)
    (hminor : ∀ y ∈ C, ∀ A : Set X, MeasurableSet A →
      ENNReal.ofReal ε * ν A ≤ iterKernel P m y A)
    (hmix : ∀ i ∈ Finset.range T,
      tvDist ((iterKernel P (N - m - i)) ∘ₘ ν) π ≤ e)
    (x : X)
    (hocc : 1 / (2 * B) ≤ ∑ i ∈ Finset.range T, (iterKernel P i x).real C)
    {A : Set X} (hA : MeasurableSet A) :
    ε / (2 * B * T) * π.real A - e ≤ (iterKernel P N x).real A := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  let w : ℕ → ℝ := fun i => (iterKernel P i x).real C
  let u : ℕ → ℝ := fun i => ((iterKernel P (N - m - i)) ∘ₘ ν).real A
  have hw0 : ∀ i, 0 ≤ w i := fun _ => ENNReal.toReal_nonneg
  have hw1 : ∀ i, w i ≤ 1 := fun i => prob_real_le_one _ _
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range T, w i := Finset.sum_nonneg fun i _ => hw0 i
  have hsum1 : (∑ i ∈ Finset.range T, w i) ≤ T := by
    calc
      (∑ i ∈ Finset.range T, w i) ≤ ∑ _i ∈ Finset.range T, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hw1 i
      _ = T := by simp
  have hu : ∀ i ∈ Finset.range T, π.real A - e ≤ u i := by
    intro i hi
    have hh := (MixtureTVConvergence.event_le_tv
      ((iterKernel P (N - m - i)) ∘ₘ ν) π hA).trans (hmix i hi)
    have hh' := (abs_le.mp hh).1
    change -e ≤ ((iterKernel P (N - m - i)) ∘ₘ ν).real A - π.real A at hh'
    dsimp [u]
    linarith
  have hprop : ∀ i ∈ Finset.range T,
      ε * w i * u i ≤ (iterKernel P N x).real A := by
    intro i hi
    have hidx : N - m - i + m + i = N := by
      have hi' := Finset.mem_range.mp hi
      omega
    simpa only [w, u, hidx] using
      propagated_minorization P C hC m ε hε0 ν hminor i (N - m - i) x hA
  have hupper : ε * (∑ i ∈ Finset.range T, w i * u i) ≤
      (T : ℝ) * (iterKernel P N x).real A := by
    have h := Finset.sum_le_sum hprop
    simpa only [mul_assoc, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] using h
  have hlower : (∑ i ∈ Finset.range T, w i) * (π.real A - e) ≤
      ∑ i ∈ Finset.range T, w i * u i := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hu i hi) (hw0 i)
  have hid : ε / (2 * B * T) * T = ε * (1 / (2 * B)) := by
    field_simp [ne_of_gt hB, ne_of_gt hTr]
  have hmass : ε / (2 * B * T) * T ≤ ε * (∑ i ∈ Finset.range T, w i) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hocc hε0
  have hmass1 : ε * (∑ i ∈ Finset.range T, w i) ≤ T := by
    have h := mul_le_mul_of_nonneg_right hε1 hsum0
    nlinarith
  have hmassA := mul_le_mul_of_nonneg_right hmass (show 0 ≤ π.real A from ENNReal.toReal_nonneg)
  have hmasse := mul_le_mul_of_nonneg_right hmass1 he
  have hlowere := mul_le_mul_of_nonneg_left hlower hε0
  apply (mul_le_mul_iff_left₀ hTr).mp
  nlinarith

theorem exists_block_diameter (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hP : HarrisErgodic P π)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (hVi : ∀ x, Integrable V (P x)) (C : Set X) (hC : MeasurableSet C)
    (hsmall : IsSmallSet P C) (a B : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hB : 1 ≤ B)
    (hdrift : ∀ x, (∫ y, V y ∂P x) ≤ a * V x + B * C.indicator (fun _ => 1) x)
    (L : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ x y, V x ≤ L → V y ≤ L →
        tvDist (iterKernel P N x) (iterKernel P N y) ≤ 1 - θ := by
  obtain ⟨m, hm, ε0, hε0, ν, hν, hminor0⟩ := hsmall
  letI : IsProbabilityMeasure ν := hν
  let ε : ℝ := min ε0 (1 / 2)
  have hε : 0 < ε := lt_min hε0 (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hminor : ∀ y ∈ C, ∀ A : Set X, MeasurableSet A →
      ENNReal.ofReal ε * ν A ≤ iterKernel P m y A := by
    intro y hy A hA
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_left _ _)) _).trans
      (hminor0 y hy A hA)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨T, hT, hocc⟩ := finite_occupation P V hV hV1 hVi C hC a B ha0 ha1 hBpos hdrift L
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : 0 < (T : ℝ) := lt_of_lt_of_le zero_lt_one hTr
  let δ : ℝ := ε / (2 * B * T)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    have hBT : (1 : ℝ) ≤ B * T := by
      simpa using mul_le_mul hB hTr zero_le_one (le_trans zero_le_one hB)
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 2 * B * (T : ℝ))).mpr
    nlinarith
  have hlim := MixtureTVConvergence.tendsto_tvDist_comp P π ν hP
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < δ / 4)))
  let N : ℕ := m + T + N0
  have hN : m + T ≤ N := by dsimp [N]; omega
  have hmix : ∀ i ∈ Finset.range T,
      tvDist ((iterKernel P (N - m - i)) ∘ₘ ν) π ≤ δ / 4 := by
    intro i hi
    apply (hN0 _ ?_).le
    have hi' := Finset.mem_range.mp hi
    dsimp [N]
    omega
  have hlower : ∀ x, V x ≤ L → ∀ A : Set X, MeasurableSet A →
      δ * π.real A - δ / 4 ≤ (iterKernel P N x).real A := by
    intro x hx A hA
    exact averaged_minorization_lower P π ν C hC m T N hT hN ε B (δ / 4)
      hε.le (by linarith) hBpos (by positivity) hminor hmix x (hocc x hx) hA
  refine ⟨N, by dsimp [N]; omega, δ / 2, by positivity, by linarith, ?_⟩
  intro x y hx hy
  apply tv_le_of_event_le
  intro A hA
  have hxA := hlower x hx A hA
  have hyA := hlower y hy A hA
  have hxAc := hlower x hx Aᶜ hA.compl
  have hyAc := hlower y hy Aᶜ hA.compl
  simp only [probReal_compl_eq_one_sub hA] at hxAc hyAc
  rw [abs_le]
  constructor <;> nlinarith

end GeoDriftBlock

end GeometricRateComponent3

section GeometricRateComponent4

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace GeometricBlockRate

set_option maxHeartbeats 2000000

variable {X : Type*} [MeasurableSpace X]

theorem tv_bound_of_centered_tests (mu pi : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure pi] (A : ℝ)
    (h : ∀ f : X → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
      (∫ x, f x ∂pi) = 0 → |∫ x, f x ∂mu| ≤ A) :
    tvDist mu pi ≤ A := by
  refine csSup_le ?_ ?_
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  rintro r ⟨s, hs, rfl⟩
  let f : X → ℝ := fun x => s.indicator (fun _ => 1) x - pi.real s
  have hp0 : 0 ≤ pi.real s := ENNReal.toReal_nonneg
  have hp1 : pi.real s ≤ 1 := by
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using (prob_le_one (μ := pi) (s := s))
  have hf : Measurable f := (measurable_const.indicator hs).sub_const _
  have hf1 : ∀ x, |f x| ≤ 1 := by
    intro x
    rw [abs_le]
    by_cases hx : x ∈ s
    · simp only [f, Set.indicator_of_mem hx]
      constructor <;> linarith
    · simp only [f, Set.indicator_of_notMem hx]
      constructor <;> linarith
  have hint (nu : Measure X) [IsProbabilityMeasure nu] :
      (∫ x, f x ∂nu) = nu.real s - pi.real s := by
    rw [show f = fun x => s.indicator (fun _ => (1 : ℝ)) x - pi.real s from rfl,
      integral_sub ((integrable_const (1 : ℝ)).indicator hs) (integrable_const _),
      integral_indicator hs]
    simp
  have hf0 : (∫ x, f x ∂pi) = 0 := by rw [hint]; ring
  simpa only [hint, measureReal_def] using h f hf hf1 hf0

theorem tv_comp_le (K : Kernel X X) [IsMarkovKernel K]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    tvDist (K ∘ₘ mu) (K ∘ₘ nu) ≤ tvDist mu nu := by
  refine csSup_le ?_ ?_
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  rintro r ⟨s, hs, rfl⟩
  rw [MixtureTVConvergence.bind_real K mu hs, MixtureTVConvergence.bind_real K nu hs]
  apply abs_integral_sub_le_tvDist mu nu (fun x => (K x s).toReal)
    (Kernel.measurable_coe K hs).ennreal_toReal (fun _ => ENNReal.toReal_nonneg)
  intro x
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  simpa using (prob_le_one (μ := K x) (s := s))

theorem iter_invariant (P : Kernel X X) (pi : Measure X)
    (hpi : Kernel.Invariant P pi) (n : ℕ) : Kernel.Invariant (iterKernel P n) pi := by
  induction n with
  | zero => simp [iterKernel_zero, Kernel.Invariant]
  | succ n ih => exact hpi.comp ih

theorem iter_block (P : Kernel X X) (N k : ℕ) :
    iterKernel (iterKernel P N) k = iterKernel P (N * k) := by
  simp only [GeoDriftBlock.iterKernel_eq_pow]
  exact (pow_mul P N k).symm

theorem remainder_tv_le (P : Kernel X X) [IsMarkovKernel P]
    (pi : Measure X) [IsProbabilityMeasure pi] (hpi : Kernel.Invariant P pi)
    (N n : ℕ) (x : X) :
    tvDist (iterKernel P n x) pi ≤ tvDist (iterKernel P (N * (n / N)) x) pi := by
  have hcomp : iterKernel P (n % N) ∘ₘ iterKernel P (N * (n / N)) x = iterKernel P n x := by
    rw [← Kernel.comp_apply, GeoDriftBlock.iterKernel_comp, Nat.mod_add_div]
  have hinv : iterKernel P (n % N) ∘ₘ pi = pi := iter_invariant P pi hpi _
  calc
    tvDist (iterKernel P n x) pi =
        tvDist (iterKernel P (n % N) ∘ₘ iterKernel P (N * (n / N)) x)
          (iterKernel P (n % N) ∘ₘ pi) := by rw [hcomp, hinv]
    _ ≤ tvDist (iterKernel P (N * (n / N)) x) pi := tv_comp_le _ _ _

theorem block_power_bound (N : ℕ) (hN : 1 ≤ N) (kappa : ℝ)
    (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    ∃ rho : ℝ, 0 < rho ∧ rho < 1 ∧
      ∀ n : ℕ, kappa ^ (n / N) ≤ kappa⁻¹ * rho ^ n := by
  let rho : ℝ := kappa ^ ((N : ℝ)⁻¹)
  have hN0 : N ≠ 0 := by omega
  have hr0 : 0 < rho := Real.rpow_pos_of_pos hk0 _
  have hr1 : rho < 1 := Real.rpow_lt_one hk0.le hk1 (by positivity)
  have hrN : rho ^ N = kappa := Real.rpow_inv_natCast_pow hk0.le hN0
  refine ⟨rho, hr0, hr1, ?_⟩
  intro n
  have hn : n ≤ N * (n / N + 1) := by
    have hmod := Nat.mod_lt n (show 0 < N by omega)
    have hdiv := Nat.mod_add_div n N
    nlinarith
  have hp := pow_le_pow_of_le_one hr0.le hr1.le hn
  rw [pow_mul, hrN, pow_succ] at hp
  calc
    kappa ^ (n / N) = kappa⁻¹ * (kappa ^ (n / N) * kappa) := by field_simp
    _ ≤ kappa⁻¹ * rho ^ n := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hk0.le)

theorem rate_of_block_bound (P : Kernel X X) [IsMarkovKernel P]
    (pi : Measure X) [IsProbabilityMeasure pi] (hpi : Kernel.Invariant P pi)
    (V : X → ℝ) (hV0 : ∀ x, 0 ≤ V x)
    (N : ℕ) (hN : 1 ≤ N) (C kappa : ℝ) (hC : 0 ≤ C)
    (hk0 : 0 < kappa) (hk1 : kappa < 1)
    (hblock : ∀ x k, tvDist (iterKernel P (N * k) x) pi ≤ C * V x * kappa ^ k) :
    ∃ R rho : ℝ, 0 ≤ R ∧ 0 ≤ rho ∧ rho < 1 ∧
      ErgodicWithRate P pi (fun x => R * V x) (fun n => rho ^ n) := by
  obtain ⟨rho, hr0, hr1, hp⟩ := block_power_bound N hN kappa hk0 hk1
  refine ⟨C * kappa⁻¹, rho, mul_nonneg hC (inv_nonneg.mpr hk0.le), hr0.le, hr1, ?_⟩
  intro x n _hn
  calc
    tvDist (iterKernel P n x) pi ≤ tvDist (iterKernel P (N * (n / N)) x) pi :=
      remainder_tv_le P pi hpi N n x
    _ ≤ C * V x * kappa ^ (n / N) := hblock x (n / N)
    _ ≤ C * V x * (kappa⁻¹ * rho ^ n) :=
      mul_le_mul_of_nonneg_left (hp n) (mul_nonneg hC (hV0 x))
    _ = C * kappa⁻¹ * V x * rho ^ n := by ring

end GeometricBlockRate

end GeometricRateComponent4

section GeometricRateComponent5

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal

namespace WeightedOscillation

set_option maxHeartbeats 2000000

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem scalar_center [Nonempty X] (f W : X → ℝ) (r : ℝ)
    (h : ∀ x y, |f x - f y| ≤ r * (W x + W y)) :
    ∃ c : ℝ, ∀ x, |f x - c| ≤ r * W x := by
  classical
  let x0 : X := Classical.choice inferInstance
  have hcross : ∀ x y, f x - r * W x ≤ f y + r * W y := by
    intro x y
    have hh := (abs_le.mp (h x y)).2
    nlinarith
  have hb : BddAbove (Set.range (fun x => f x - r * W x)) := by
    refine ⟨f x0 + r * W x0, ?_⟩
    rintro z ⟨x, rfl⟩
    exact hcross x x0
  refine ⟨sSup (Set.range (fun x => f x - r * W x)), ?_⟩
  intro x
  have hl := le_csSup hb (Set.mem_range_self x)
  have hu : sSup (Set.range (fun x => f x - r * W x)) ≤ f x + r * W x := by
    apply csSup_le (Set.range_nonempty _)
    rintro z ⟨y, rfl⟩
    exact hcross y x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem bounded_integrable (mu : Measure X) [IsFiniteMeasure mu]
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ x, |f x| ≤ B) :
    Integrable f mu := by
  apply Integrable.of_bound hf.aestronglyMeasurable B
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using hb x

theorem abs_integral_le_bound (mu : Measure X) [IsProbabilityMeasure mu]
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂mu| ≤ B := by
  calc
    |∫ x, f x ∂mu| ≤ ∫ x, |f x| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ _x : X, B ∂mu :=
      integral_mono (bounded_integrable mu f hf B hb).abs (integrable_const _) hb
    _ = B := by simp

theorem abs_integral_sub_le_two_tv (mu nu : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : X → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| ≤ 2 * tvDist mu nu := by
  let g := fun x => (f x + 1) / 2
  have hg : Measurable g := (hf.add_const 1).div_const 2
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    have hh := (abs_le.mp (hb x)).1
    dsimp [g]
    linarith
  have hg1 : ∀ x, g x ≤ 1 := fun x => by
    have hh := (abs_le.mp (hb x)).2
    dsimp [g]
    linarith
  have ht := abs_integral_sub_le_tvDist mu nu g hg hg0 hg1
  have hi (m : Measure X) [IsProbabilityMeasure m] :
      (∫ x, g x ∂m) = ((∫ x, f x ∂m) + 1) / 2 := by
    dsimp [g]
    rw [integral_div, integral_add (bounded_integrable m f hf 1 hb) (integrable_const _)]
    simp
  rw [hi mu, hi nu] at ht
  have heq : ((∫ x, f x ∂mu) + 1) / 2 - ((∫ x, f x ∂nu) + 1) / 2 =
      ((∫ x, f x ∂mu) - (∫ x, f x ∂nu)) / 2 := by ring
  rw [heq, abs_div] at ht
  norm_num at ht
  linarith

noncomputable def clip (z : ℝ) : ℝ := max (-1) (min 1 z)

theorem clip_abs (z : ℝ) : |clip z| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clip_residual (z t : ℝ) (ht : 0 ≤ t) (hz : |z| ≤ 1 + t) :
    |z - clip z| ≤ t := by
  rcases le_total z (-1) with h | h
  · have hm : min 1 z = z := min_eq_right (by linarith)
    simp only [clip, hm, max_eq_left h]
    rw [abs_of_nonpos (by linarith)]
    have := (abs_le.mp hz).1
    linarith
  · rcases le_total z 1 with h1 | h1
    · simp only [clip, min_eq_right h1, max_eq_right h, sub_self, abs_zero]
      exact ht
    · simp only [clip, min_eq_left h1, show max (-1 : ℝ) 1 = 1 by norm_num]
      rw [abs_of_nonneg (by linarith)]
      have := (abs_le.mp hz).2
      linarith

theorem weighted_integrable (mu : Measure X) [IsFiniteMeasure mu]
    (f V : X → ℝ) (hf : Measurable f) (hVi : Integrable V mu) (beta : ℝ)
    (hb : ∀ x, |f x| ≤ 1 + beta * V x) : Integrable f mu := by
  apply ((integrable_const 1).add (hVi.const_mul beta)).mono' hf.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using hb x

theorem weighted_integral_bound (mu : Measure X) [IsProbabilityMeasure mu]
    (f V : X → ℝ) (hf : Measurable f) (hVi : Integrable V mu) (beta : ℝ)
    (hb : ∀ x, |f x| ≤ 1 + beta * V x) :
    |∫ x, f x ∂mu| ≤ 1 + beta * (∫ x, V x ∂mu) := by
  calc
    |∫ x, f x ∂mu| ≤ ∫ x, |f x| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ x, 1 + beta * V x ∂mu :=
      integral_mono (weighted_integrable mu f V hf hVi beta hb).abs
        ((integrable_const 1).add (hVi.const_mul beta)) hb
    _ = 1 + beta * (∫ x, V x ∂mu) := by
      rw [integral_add (integrable_const 1) (hVi.const_mul beta), integral_const_mul]
      simp

theorem weighted_difference_bound (mu nu : Measure X)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f V : X → ℝ) (hf : Measurable f) (hV0 : ∀ x, 0 ≤ V x)
    (hVmu : Integrable V mu) (hVnu : Integrable V nu)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hb : ∀ x, |f x| ≤ 1 + beta * V x) :
    |(∫ x, f x ∂mu) - (∫ x, f x ∂nu)| ≤
      2 * tvDist mu nu + beta * ((∫ x, V x ∂mu) + (∫ x, V x ∂nu)) := by
  let g := fun x => clip (f x)
  have hg : Measurable g := measurable_const.max (measurable_const.min hf)
  have hgb : ∀ x, |g x| ≤ 1 := fun x => clip_abs _
  have hr : ∀ x, |f x - g x| ≤ beta * V x := fun x =>
    clip_residual _ _ (mul_nonneg hbeta (hV0 x)) (hb x)
  have hri (m : Measure X) [IsProbabilityMeasure m] (hVm : Integrable V m) :
      Integrable (fun x => f x - g x) m :=
    (weighted_integrable m f V hf hVm beta hb).sub (bounded_integrable m g hg 1 hgb)
  have hres (m : Measure X) [IsProbabilityMeasure m] (hVm : Integrable V m) :
      |∫ x, f x - g x ∂m| ≤ beta * ∫ x, V x ∂m := by
    calc
      |∫ x, f x - g x ∂m| ≤ ∫ x, |f x - g x| ∂m := abs_integral_le_integral_abs
      _ ≤ ∫ x, beta * V x ∂m := integral_mono (hri m hVm).abs (hVm.const_mul beta) hr
      _ = _ := integral_const_mul _ _
  have heq : (∫ x, f x ∂mu) - (∫ x, f x ∂nu) =
      ((∫ x, g x ∂mu) - (∫ x, g x ∂nu)) +
        (∫ x, f x - g x ∂mu) - (∫ x, f x - g x ∂nu) := by
    rw [integral_sub (weighted_integrable mu f V hf hVmu beta hb)
      (bounded_integrable mu g hg 1 hgb),
      integral_sub (weighted_integrable nu f V hf hVnu beta hb)
      (bounded_integrable nu g hg 1 hgb)]
    ring
  rw [heq]
  calc
    _ ≤ |(∫ x, g x ∂mu) - (∫ x, g x ∂nu)| +
        |∫ x, f x - g x ∂mu| + |∫ x, f x - g x ∂nu| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * tvDist mu nu + beta * ((∫ x, V x ∂mu) + (∫ x, V x ∂nu)) := by
      have := abs_integral_sub_le_two_tv mu nu g hg hgb
      have := hres mu hVmu
      have := hres nu hVnu
      linarith

theorem contraction (Q : Kernel X X) [IsMarkovKernel Q]
    (V : X → ℝ) (hV0 : ∀ x, 0 ≤ V x) (hVi : ∀ x, Integrable V (Q x))
    (a K L theta : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hK : 0 < K)
    (hL : 0 < L) (hgap : 2 * K < (1 - a) * L)
    (ht0 : 0 < theta) (ht1 : theta < 1)
    (hd : ∀ x, (∫ y, V y ∂Q x) ≤ a * V x + K)
    (htv : ∀ x y, V x ≤ L → V y ≤ L → tvDist (Q x) (Q y) ≤ 1 - theta) :
    ∃ beta kappa : ℝ, 0 < beta ∧ 0 < kappa ∧ kappa < 1 ∧
      ∀ f : X → ℝ, Measurable f → (∀ x, |f x| ≤ 1 + beta * V x) →
      ∀ x y, |(∫ z, f z ∂Q x) - (∫ z, f z ∂Q y)| ≤
        kappa * ((1 + beta * V x) + (1 + beta * V y)) := by
  let beta := theta / (2 * K)
  have hb : 0 < beta := div_pos ht0 (by positivity)
  have hbk : 2 * beta * K = theta := by dsimp [beta]; field_simp
  let gamma := (2 + beta * a * L + 2 * beta * K) / (2 + beta * L)
  have hden : 0 < 2 + beta * L := by positivity
  have hg0 : 0 < gamma := div_pos (by positivity) hden
  have hga : a ≤ gamma := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hg1 : gamma < 1 := by
    apply (div_lt_one hden).mpr
    have := mul_lt_mul_of_pos_left hgap hb
    nlinarith
  have hgeq : gamma * (2 + beta * L) = 2 + beta * a * L + 2 * beta * K :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  let kappa := max (1 - theta / 2) (max a gamma)
  have hk0 : 0 < kappa := lt_of_lt_of_le (by linarith : 0 < 1 - theta / 2) (le_max_left _ _)
  have hk1 : kappa < 1 := max_lt (by linarith) (max_lt ha1 hg1)
  have hkta : 1 - theta / 2 ≤ kappa := le_max_left _ _
  have hka : a ≤ kappa := (le_max_left _ _).trans (le_max_right _ _)
  have hkg : gamma ≤ kappa := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨beta, kappa, hb, hk0, hk1, ?_⟩
  intro f hf hfb x y
  let S := V x + V y
  have hs : 0 ≤ S := add_nonneg (hV0 x) (hV0 y)
  have hsum : (∫ z, V z ∂Q x) + (∫ z, V z ∂Q y) ≤ a * S + 2 * K := by
    have := hd x
    have := hd y
    dsimp [S]
    linarith
  have hweight : (1 + beta * V x) + (1 + beta * V y) = 2 + beta * S := by
    dsimp [S]
    ring
  rw [hweight]
  rcases le_total S L with hsmall | hlarge
  · have hx : V x ≤ L := by dsimp [S] at hsmall; linarith [hV0 y]
    have hy : V y ≤ L := by dsimp [S] at hsmall; linarith [hV0 x]
    have hh := weighted_difference_bound (Q x) (Q y) f V hf hV0 (hVi x) (hVi y)
      beta hb.le hfb
    have htvxy := htv x y hx hy
    have hbs := mul_le_mul_of_nonneg_left hsum hb.le
    have hks := mul_le_mul_of_nonneg_right hka (mul_nonneg hb.le hs)
    nlinarith
  · have hfx := weighted_integral_bound (Q x) f V hf (hVi x) beta hfb
    have hfy := weighted_integral_bound (Q y) f V hf (hVi y) beta hfb
    have htri := abs_sub (∫ z, f z ∂Q x) (∫ z, f z ∂Q y)
    have hbs := mul_le_mul_of_nonneg_left hsum hb.le
    have hgS : 2 + beta * a * S + 2 * beta * K ≤ gamma * (2 + beta * S) := by
      have := mul_nonneg (sub_nonneg.mpr hga) (mul_nonneg hb.le (sub_nonneg.mpr hlarge))
      nlinarith [hgeq]
    have hkgS := mul_le_mul_of_nonneg_right hkg (by positivity : 0 ≤ 2 + beta * S)
    nlinarith

end WeightedOscillation

end GeometricRateComponent5

section GeometricRateComponent6

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal ProbabilityTheory

namespace WeightedOscillation

set_option maxHeartbeats 2000000

variable {X : Type*} [MeasurableSpace X]

/- This complete lemma retains KernelL2.lean lines 48-57, SHA256
c51778d818c9dd8546fd1d6c13d44136cc48d868571083c3c8667e68458a154a.
The complete source and accepted-source provenance are retained in this packet. -/
theorem integral_invariant (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    {f : X → ℝ} (hf : Integrable f π) :
    (∫ x, ∫ y, f y ∂P x ∂π) = ∫ x, f x ∂π := by
  change P ∘ₘ π = π at hinv
  have hcomp : Integrable f ((P ∘ₖ Kernel.const Unit π) ()) := by
    simpa only [← Measure.comp_eq_comp_const_apply, hinv] using hf
  simpa only [← Measure.comp_eq_comp_const_apply, hinv, Kernel.const_apply] using
    (Kernel.integral_comp hcomp).symm

theorem iter_right_succ (Q : Kernel X X) (n : ℕ) :
    iterKernel Q (n + 1) = iterKernel Q n ∘ₖ Q := by
  simp only [GeoDriftBlock.iterKernel_eq_pow]
  exact pow_succ Q n

theorem iter_pair_bound [Nonempty X] (Q : Kernel X X) [IsMarkovKernel Q]
    (V : X → ℝ) (hV0 : ∀ x, 0 ≤ V x) (beta kappa : ℝ)
    (hb : 0 ≤ beta) (hk : 0 < kappa)
    (hstep : ∀ f : X → ℝ, Measurable f → (∀ x, |f x| ≤ 1 + beta * V x) →
      ∀ x y, |(∫ z, f z ∂Q x) - (∫ z, f z ∂Q y)| ≤
        kappa * ((1 + beta * V x) + (1 + beta * V y)))
    (f : X → ℝ) (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1) :
    ∀ n : ℕ, ∀ x y,
      |(∫ z, f z ∂iterKernel Q n x) - (∫ z, f z ∂iterKernel Q n y)| ≤
        kappa ^ n * ((1 + beta * V x) + (1 + beta * V y)) := by
  let F : ℕ → X → ℝ := fun n x => ∫ z, f z ∂iterKernel Q n x
  have hFm (n : ℕ) : Measurable (F n) := hf.stronglyMeasurable.integral_kernel.measurable
  have hFb (n : ℕ) (x : X) : |F n x| ≤ 1 :=
    abs_integral_le_bound (iterKernel Q n x) f hf 1 hfb
  have hrec (n : ℕ) (x : X) : F (n + 1) x = ∫ y, F n y ∂Q x := by
    change (∫ z, f z ∂iterKernel Q (n + 1) x) =
      ∫ y, (∫ z, f z ∂iterKernel Q n y) ∂Q x
    rw [iter_right_succ]
    exact Kernel.integral_comp (bounded_integrable _ f hf 1 hfb)
  intro n
  change ∀ x y, |F n x - F n y| ≤ kappa ^ n * ((1 + beta * V x) + (1 + beta * V y))
  induction n with
  | zero =>
      intro x y
      have hx : F 0 x = f x := by
        change (∫ z, f z ∂Measure.dirac x) = f x
        exact integral_dirac' f x hf.stronglyMeasurable
      have hy : F 0 y = f y := by
        change (∫ z, f z ∂Measure.dirac y) = f y
        exact integral_dirac' f y hf.stronglyMeasurable
      rw [hx, hy, pow_zero, one_mul]
      have hh := (abs_sub (f x) (f y)).trans (add_le_add (hfb x) (hfb y))
      have := mul_nonneg hb (hV0 x)
      have := mul_nonneg hb (hV0 y)
      linarith
  | succ n ih =>
      obtain ⟨c, hc⟩ := scalar_center (F n) (fun x => 1 + beta * V x) (kappa ^ n) ih
      have hkn : 0 < kappa ^ n := pow_pos hk n
      let g : X → ℝ := fun x => (F n x - c) / kappa ^ n
      have hgm : Measurable g := ((hFm n).sub_const c).div_const _
      have hgb : ∀ x, |g x| ≤ 1 + beta * V x := by
        intro x
        dsimp [g]
        rw [abs_div, abs_of_pos hkn]
        apply (div_le_iff₀ hkn).mpr
        simpa only [mul_comm] using hc x
      have hgi (x : X) : (∫ z, g z ∂Q x) = (F (n + 1) x - c) / kappa ^ n := by
        dsimp [g]
        rw [integral_div, integral_sub (bounded_integrable _ (F n) (hFm n) 1 (hFb n))
          (integrable_const _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, ← hrec]
      intro x y
      have hs := hstep g hgm hgb x y
      rw [hgi x, hgi y] at hs
      have heq : (F (n + 1) x - c) / kappa ^ n - (F (n + 1) y - c) / kappa ^ n =
          (F (n + 1) x - F (n + 1) y) / kappa ^ n := by ring
      rw [heq, abs_div, abs_of_pos hkn] at hs
      calc
        |F (n + 1) x - F (n + 1) y| ≤
            (kappa * ((1 + beta * V x) + (1 + beta * V y))) * kappa ^ n :=
          (div_le_iff₀ hkn).mp hs
        _ = kappa ^ (n + 1) * ((1 + beta * V x) + (1 + beta * V y)) := by
          rw [pow_succ]
          ring

theorem centered_iter_bound (Q : Kernel X X) [IsMarkovKernel Q]
    (pi : Measure X) [IsProbabilityMeasure pi] (hpi : Kernel.Invariant Q pi)
    (V : X → ℝ) (hV1 : ∀ x, 1 ≤ V x) (hVi : Integrable V pi)
    (beta kappa : ℝ) (hb : 0 ≤ beta) (hk : 0 < kappa)
    (hstep : ∀ f : X → ℝ, Measurable f → (∀ x, |f x| ≤ 1 + beta * V x) →
      ∀ x y, |(∫ z, f z ∂Q x) - (∫ z, f z ∂Q y)| ≤
        kappa * ((1 + beta * V x) + (1 + beta * V y))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : X → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
      (∫ x, f x ∂pi) = 0 → ∀ n : ℕ, ∀ x,
      |∫ z, f z ∂iterKernel Q n x| ≤ C * V x * kappa ^ n := by
  letI : Nonempty X := nonempty_of_isProbabilityMeasure pi
  have hV0 : ∀ x, 0 ≤ V x := fun x => le_trans zero_le_one (hV1 x)
  let C := 2 + beta + beta * ∫ x, V x ∂pi
  have hmean : 0 ≤ ∫ x, V x ∂pi := integral_nonneg hV0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hf hfb hf0 n x
  let F : X → ℝ := fun y => ∫ z, f z ∂iterKernel Q n y
  have hFm : Measurable F := hf.stronglyMeasurable.integral_kernel.measurable
  have hFb : ∀ y, |F y| ≤ 1 := fun y =>
    abs_integral_le_bound (iterKernel Q n y) f hf 1 hfb
  have hFi : Integrable F pi := bounded_integrable pi F hFm 1 hFb
  have hF0 : (∫ y, F y ∂pi) = 0 := by
    rw [show (∫ y, F y ∂pi) = ∫ y, f y ∂pi from
      integral_invariant (iterKernel Q n) pi (GeometricBlockRate.iter_invariant Q pi hpi n)
        (bounded_integrable pi f hf 1 hfb), hf0]
  have hpair := iter_pair_bound Q V hV0 beta kappa hb hk hstep f hf hfb n
  have heq : (∫ y, F x - F y ∂pi) = F x := by
    rw [integral_sub (integrable_const _) hFi, integral_const, hF0]
    simp
  have hW : Integrable (fun y => kappa ^ n * ((1 + beta * V x) + (1 + beta * V y))) pi :=
    ((integrable_const _).add ((integrable_const 1).add (hVi.const_mul beta))).const_mul _
  have hbound : |F x| ≤ kappa ^ n * (2 + beta * V x + beta * ∫ y, V y ∂pi) := by
    calc
      |F x| = |∫ y, F x - F y ∂pi| := by rw [heq]
      _ ≤ ∫ y, |F x - F y| ∂pi := abs_integral_le_integral_abs
      _ ≤ ∫ y, kappa ^ n * ((1 + beta * V x) + (1 + beta * V y)) ∂pi :=
        integral_mono ((integrable_const _).sub hFi).abs hW (hpair x)
      _ = _ := by
        rw [integral_const_mul, integral_add (f := fun _ : X => 1 + beta * V x)
          (g := fun y => 1 + beta * V y) (integrable_const _)
          ((integrable_const 1).add (hVi.const_mul beta)),
          integral_add (f := fun _ : X => (1 : ℝ)) (g := fun y => beta * V y)
            (integrable_const 1) (hVi.const_mul beta), integral_const_mul]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        ring
  have hconstant : 2 + beta * V x + beta * ∫ y, V y ∂pi ≤ C * V x := by
    have hm := mul_nonneg hb hmean
    have hh := mul_le_mul_of_nonneg_left (hV1 x) (by positivity : 0 ≤ 2 + beta * ∫ y, V y ∂pi)
    dsimp [C]
    nlinarith
  calc
    |∫ z, f z ∂iterKernel Q n x| ≤ kappa ^ n * (2 + beta * V x + beta * ∫ y, V y ∂pi) := hbound
    _ ≤ kappa ^ n * (C * V x) := mul_le_mul_of_nonneg_left hconstant (pow_nonneg hk.le n)
    _ = C * V x * kappa ^ n := by ring

end WeightedOscillation

end GeometricRateComponent6

section GeometricRateComponent7

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C) :
    ∃ R ρ : ℝ, 0 ≤ R ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ErgodicWithRate P π (fun x => R * V x) (fun n => ρ ^ n) := by
  have hV0 : ∀ x, 0 ≤ V x := fun x => le_trans zero_le_one (hV1 x)
  have hVpi := MarkovChainCLT.integrable_of_geoDriftCondition P π hP V hV hV1 C hC hsmall d b hd hdrift
  obtain ⟨a, B, ha0, ha1, hB, hab⟩ :=
    GeoDriftBlock.normalize_drift P V hV1 C d b hd hdrift
  have hapos : 0 < 1 - a := by linarith
  let K : ℝ := B / (1 - a)
  have hK : 0 < K := div_pos (by linarith) hapos
  let L : ℝ := (2 * K + 1) / (1 - a)
  have hL : 0 < L := div_pos (by positivity) hapos
  have hLeq : (1 - a) * L = 2 * K + 1 := by
    dsimp [L]
    field_simp [ne_of_gt hapos]
  have hgap : 2 * K < (1 - a) * L := by linarith
  obtain ⟨N, hN, theta, ht0, ht1, htv⟩ :=
    GeoDriftBlock.exists_block_diameter P π hP V hV hV1 hdrift.1 C hC hsmall a B ha0.le ha1 hB hab L
  have hQi : ∀ x, Integrable V (MarkovChainCLT.iterKernel P N x) :=
    GeoDriftBlock.iter_integrable P V hV hV0 hdrift.1 C a B ha1.le (by linarith) hab N
  have hQd : ∀ x, (∫ y, V y ∂MarkovChainCLT.iterKernel P N x) ≤ a * V x + K := by
    intro x
    have hbound := GeoDriftBlock.iter_global_bound P V hV hV0 hdrift.1 C a B ha0.le ha1
      (by linarith) hab N x
    have hpow : a ^ N ≤ a := by simpa using pow_le_pow_of_le_one ha0.le ha1.le hN
    have hmul := mul_le_mul_of_nonneg_right hpow (hV0 x)
    exact hbound.trans (by dsimp [K]; linarith)
  obtain ⟨beta, kappa, hb0, hk0, hk1, hstep⟩ :=
    WeightedOscillation.contraction (MarkovChainCLT.iterKernel P N) V hV0 hQi
      a K L theta ha0.le ha1 hK hL hgap ht0 ht1 hQd htv
  obtain ⟨A, hA, hcenter⟩ :=
    WeightedOscillation.centered_iter_bound (MarkovChainCLT.iterKernel P N) π
      (GeometricBlockRate.iter_invariant P π hP.1 N) V hV1 hVpi beta kappa hb0.le hk0 hstep
  apply GeometricBlockRate.rate_of_block_bound P π hP.1 V hV0 N hN A kappa hA hk0 hk1
  intro x k
  rw [← GeometricBlockRate.iter_block]
  apply GeometricBlockRate.tv_bound_of_centered_tests
  intro f hf hfb hf0
  exact hcenter f hf hfb hf0 k x

end GeometricRateComponent7

