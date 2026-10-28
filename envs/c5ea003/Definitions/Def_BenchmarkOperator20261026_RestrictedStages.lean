-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedStages
-- name    : BenchmarkOperator20261026_RestrictedStages
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:39:58.189715+00:00
-- url     : https://prove2.me/theorems/bd0625ec-d0f7-4b59-bf3e-e911c63909d2
-- title:
--   Restricted Stages
-- statement:
--   Defines real sequence space, the finite-head/infinite-tail equivalence, stage sets, the tail product probability and the stage measures. The retained restriction, support and coordinate identities, with their structure instances, make these finite-stage constructions available.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedStages.lean, lines 16–207; source SHA-256 492384755dd125aa336a1d7c000a059c1effb1d57e9ac9fb4b7dd51d1068e9ed. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false

namespace MeasurableEquiv
end MeasurableEquiv
namespace MeasureEquivalenceCompactAveraging
end MeasureEquivalenceCompactAveraging
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
namespace MeasureEquivalenceDensityGraph
end MeasureEquivalenceDensityGraph
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
namespace MeasureEquivalenceEquidecomposition.greedyRemainder
end MeasureEquivalenceEquidecomposition.greedyRemainder
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
namespace MeasureEquivalenceInvariantGraph
end MeasureEquivalenceInvariantGraph
namespace MeasureEquivalenceInverseAC
end MeasureEquivalenceInverseAC
namespace MeasureEquivalenceL2Coefficients
end MeasureEquivalenceL2Coefficients
namespace MeasureEquivalenceL2Restriction
end MeasureEquivalenceL2Restriction
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
namespace MeasureEquivalenceMarkov.kernelIterate
end MeasureEquivalenceMarkov.kernelIterate
namespace MeasureEquivalenceRNGraph
end MeasureEquivalenceRNGraph
namespace MeasureEquivalenceRNPresentation
end MeasureEquivalenceRNPresentation
namespace MeasureEquivalenceResearch
end MeasureEquivalenceResearch
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages
end MeasureEquivalenceRestrictedProduct.CompatibleStages
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
end MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
namespace MeasureEquivalenceRestrictedRoots
end MeasureEquivalenceRestrictedRoots
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
namespace MeasureEquivalenceSharedDensity
end MeasureEquivalenceSharedDensity
namespace MeasureEquivalenceSolenoid
end MeasureEquivalenceSolenoid
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
namespace MeasureUnitary
end MeasureUnitary
namespace MeasureUnitary.FiniteBorelSection
end MeasureUnitary.FiniteBorelSection
namespace OperatorCoding
end OperatorCoding
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace lp
end lp

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

abbrev RealSequences := ℕ → ℝ

def headTailEquiv (n : ℕ) : RealSequences ≃ᵐ ((Fin n → ℝ) × RealSequences) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (finSumNatEquiv n)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ ℕ => ℝ))

@[simp] theorem headTailEquiv_head (n : ℕ) (x : RealSequences) (i : Fin n) :
    (headTailEquiv n x).1 i = x i := rfl

@[simp] theorem headTailEquiv_tail (n : ℕ) (x : RealSequences) (k : ℕ) :
    (headTailEquiv n x).2 k = x (n + k) := rfl

@[simp] theorem headTailEquiv_symm_tail (n : ℕ)
    (x : (Fin n → ℝ) × RealSequences) (k : ℕ) :
    (headTailEquiv n).symm x (n + k) = x.2 k := by
  have h := congrArg (fun z : (Fin n → ℝ) × RealSequences => z.2 k)
    ((headTailEquiv n).apply_symm_apply x)
  exact h

@[simp] theorem headTailEquiv_symm_head (n : ℕ)
    (x : (Fin n → ℝ) × RealSequences) (i : Fin n) :
    (headTailEquiv n).symm x i = x.1 i := by
  exact congrArg (fun z : (Fin n → ℝ) × RealSequences => z.1 i)
    ((headTailEquiv n).apply_symm_apply x)

def stageSet (n : ℕ) : Set RealSequences := {x | ∀ k, n ≤ k → x k ∈ baseInterval}

theorem measurable_stageSet (n : ℕ) : MeasurableSet (stageSet n) := by
  simpa only [stageSet, Set.setOf_forall] using MeasurableSet.iInter (fun k : ℕ => MeasurableSet.iInter (fun _ : n ≤ k =>
    (measurable_pi_apply k) (show MeasurableSet baseInterval from measurableSet_Icc)))



def tailProbability : Measure RealSequences := Measure.infinitePi (fun _ : ℕ => baseMeasure)

instance _root_.MeasureEquivalenceRestrictedProduct.instIsProbabilityMeasureRealSequencesTailProbability : IsProbabilityMeasure tailProbability := by unfold tailProbability; infer_instance

instance _root_.MeasureEquivalenceRestrictedProduct.instNoAtomsRealSequencesTailProbability : NoAtoms tailProbability := by
  constructor
  intro x
  have hm : tailProbability.map (fun y => y 0) = baseMeasure :=
    Measure.infinitePi_map_eval (fun _ : ℕ => baseMeasure) 0
  have he : tailProbability ((fun y => y 0) ⁻¹' {x 0}) = 0 := by
    rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton (x 0)),
      hm, measure_singleton]
  apply measure_mono_null _ he
  intro y hy
  exact congrFun (mem_singleton_iff.mp hy) 0

def stageMeasure (n : ℕ) : Measure RealSequences :=
  ((Measure.pi (fun _ : Fin n => exponentialMeasure)).prod tailProbability).map
    (headTailEquiv n).symm

instance stageMeasure_sigmaFinite (n : ℕ) : SigmaFinite (stageMeasure n) := by
  unfold stageMeasure
  exact (headTailEquiv n).symm.sigmaFinite_map

instance stageMeasure_noAtoms (n : ℕ) : NoAtoms (stageMeasure n) := by
  constructor
  intro x
  unfold stageMeasure
  rw [Measure.map_apply (headTailEquiv n).symm.measurable (measurableSet_singleton x)]
  have he : (headTailEquiv n).symm ⁻¹' {x} = {headTailEquiv n x} := by
    ext z
    exact (headTailEquiv n).toEquiv.symm_apply_eq
  rw [he, measure_singleton]



theorem ae_base_tailProbability : ∀ᵐ x ∂tailProbability, ∀ k, x k ∈ baseInterval := by
  rw [ae_all_iff]
  intro k
  have hm : tailProbability.map (fun x => x k) = baseMeasure :=
    Measure.infinitePi_map_eval (fun _ : ℕ => baseMeasure) k
  have he : ∀ᵐ t ∂baseMeasure, t ∈ baseInterval :=
    ae_restrict_mem (show MeasurableSet baseInterval from measurableSet_Icc)
  rw [← hm] at he
  have hpull : ∀ᵐ x ∂tailProbability, x k ∈ baseInterval :=
    (ae_map_iff (measurable_pi_apply k).aemeasurable
      (show MeasurableSet {t : ℝ | t ∈ baseInterval} from measurableSet_Icc)).mp he
  exact hpull

theorem ae_mem_stageMeasure (n : ℕ) : ∀ᵐ x ∂stageMeasure n, x ∈ stageSet n := by
  unfold stageMeasure
  apply (ae_map_iff (headTailEquiv n).symm.measurable.aemeasurable
    (measurable_stageSet n)).mpr
  apply (Measure.ae_prod_iff_ae_ae ((headTailEquiv n).symm.measurable (measurable_stageSet n))).mpr
  apply ae_of_all
  intro head
  filter_upwards [ae_base_tailProbability] with tail ht
  intro k hk
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa only [headTailEquiv_symm_tail] using ht r

theorem stageMeasure_restrict_self (n : ℕ) :
    (stageMeasure n).restrict (stageSet n) = stageMeasure n :=
  Measure.restrict_eq_self_of_ae_mem (ae_mem_stageMeasure n)

theorem base_head_tail_reassemble (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => baseMeasure)).prod tailProbability).map
      (headTailEquiv n).symm = tailProbability := by
  have hsum := infinitePi_sum (fun _ : Fin n => baseMeasure) (fun _ : ℕ => baseMeasure)
  have hfamily : Sum.elim (fun _ : Fin n => baseMeasure) (fun _ : ℕ => baseMeasure) =
      (fun _ : Fin n ⊕ ℕ => baseMeasure) := by funext i; cases i <;> rfl
  rw [hfamily, Measure.infinitePi_eq_pi] at hsum
  let e := MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (finSumNatEquiv n)
  calc
    ((Measure.pi (fun _ : Fin n => baseMeasure)).prod tailProbability).map
        (headTailEquiv n).symm =
      (((Measure.pi (fun _ : Fin n => baseMeasure)).prod tailProbability).map
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ ℕ => ℝ)).symm).map e := by
      rw [Measure.map_map e.measurable (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable]
      rfl
    _ = (Measure.infinitePi (fun _ : Fin n ⊕ ℕ => baseMeasure)).map e := by
      dsimp only [tailProbability]
      rw [hsum]
    _ = tailProbability :=
      Measure.infinitePi_map_piCongrLeft (fun _ : ℕ => baseMeasure) (finSumNatEquiv n)

theorem stageMeasure_restrict_base (n : ℕ) :
    (stageMeasure n).restrict (stageSet 0) = tailProbability := by
  let H : Set (Fin n → ℝ) := Set.univ.pi (fun _ => baseInterval)
  let T : Set RealSequences := {x | ∀ k, x k ∈ baseInterval}
  have hpre : (headTailEquiv n).symm ⁻¹' stageSet 0 = H ×ˢ T := by
    ext z
    change (∀ k, 0 ≤ k → (headTailEquiv n).symm z k ∈ baseInterval) ↔
      ((∀ i : Fin n, i ∈ Set.univ → z.1 i ∈ baseInterval) ∧ ∀ k, z.2 k ∈ baseInterval)
    constructor
    · intro hz
      constructor
      · intro i _
        simpa only [headTailEquiv_symm_head] using hz (i : ℕ) (Nat.zero_le _)
      · intro k
        simpa only [headTailEquiv_symm_tail] using hz (n + k) (Nat.zero_le _)
    · rintro ⟨hh, ht⟩ k _
      by_cases hk : k < n
      · rw [headTailEquiv_symm_head n z ⟨k, hk⟩]
        exact hh ⟨k, hk⟩ (mem_univ _)
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hk)
        simpa only [headTailEquiv_symm_tail] using ht r
  have ht : tailProbability.restrict T = tailProbability :=
    Measure.restrict_eq_self_of_ae_mem ae_base_tailProbability
  unfold stageMeasure
  rw [(headTailEquiv n).symm.restrict_map, hpre, ← Measure.prod_restrict,
    ht, Measure.restrict_pi_pi]
  exact base_head_tail_reassemble n

theorem stageMeasure_zero : stageMeasure 0 = tailProbability := by
  have he : (fun _ : Fin 0 => exponentialMeasure) = (fun _ : Fin 0 => baseMeasure) :=
    funext (fun i => Fin.elim0 i)
  unfold stageMeasure
  rw [he]
  exact base_head_tail_reassemble 0

theorem map_add_stageMeasure (n : ℕ) (h : RealSequences)
    (hh : ∀ k, n ≤ k → h k = 0) :
    (stageMeasure n).map (fun x => x + h) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, h i)) • stageMeasure n := by
  let g : (Fin n → ℝ) → (Fin n → ℝ) := fun x i => x i + h i
  have hg : Measurable g := by
    dsimp only [g]
    exact measurable_pi_lambda _ (fun i : Fin n =>
      (show Measurable (fun x : Fin n → ℝ => x i) from measurable_pi_apply i).add_const (h (i : ℕ)))
  have hadd : Measurable (fun x : RealSequences => x + h) := measurable_id.add_const h
  have hcomm : (fun x : RealSequences => x + h) ∘ (headTailEquiv n).symm =
      (headTailEquiv n).symm ∘ Prod.map g id := by
    funext z
    apply (headTailEquiv n).injective
    apply Prod.ext
    · funext i
      simp only [Function.comp_apply, headTailEquiv_head,
        MeasurableEquiv.apply_symm_apply, Pi.add_apply, headTailEquiv_symm_head,
        Prod.map_fst, g]
    · funext k
      simp only [Function.comp_apply, headTailEquiv_tail,
        MeasurableEquiv.apply_symm_apply, Pi.add_apply, headTailEquiv_symm_tail,
        Prod.map_snd, id_eq, hh (n + k) (Nat.le_add_right n k), add_zero]
  unfold stageMeasure
  rw [Measure.map_map hadd (headTailEquiv n).symm.measurable, hcomm,
    ← Measure.map_map (headTailEquiv n).symm.measurable (hg.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hg measurable_id, Measure.map_id]
  change (((Measure.pi fun _ : Fin n => exponentialMeasure).map
    (fun (x : Fin n → ℝ) (i : Fin n) => x i + h (i : ℕ))).prod tailProbability).map (headTailEquiv n).symm = _
  rw [pi_map_add_exponentialMeasure (fun i : Fin n => h (i : ℕ)), ENNReal.smul_def,
    coe_expNNReal, Measure.prod_smul_left, Measure.map_smul]

end MeasureEquivalenceRestrictedProduct


