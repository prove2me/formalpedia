-- Prove2me | solution 1 for BenchmarkComparisons.free_representations_borelBireducible_operators
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:01:32.503506+00:00
-- url     : https://prove2.me/submissions/000b355b-6efa-4390-b340-1f5fc8e39a29

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_OperatorAmplification
import Definitions.Def_BenchmarkOperator20261026_OperatorBireduction
import Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
import Definitions.Def_BenchmarkOperator20261026_OperatorCoefficients
import Definitions.Def_BenchmarkOperator20261026_OperatorConjugation
import Definitions.Def_BenchmarkOperator20261026_OperatorEigenspaces
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorHilbertFlatten
import Definitions.Def_BenchmarkOperator20261026_OperatorNormalization
import Definitions.Def_BenchmarkOperator20261026_OperatorSeries
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Definitions.Def_BenchmarkOperator20261026_OperatorUnitaryBorel
import Definitions.Def_BenchmarkRelations
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

namespace BenchmarkComparisons
end BenchmarkComparisons
namespace ContinuousMap
end ContinuousMap
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
namespace OperatorCoding.greedyCyclicGenerator
end OperatorCoding.greedyCyclicGenerator
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace SpectralDomination
end SpectralDomination
namespace lp
end lp


/- Preserved source skeleton: OperatorFreeGroup -/
section Source0
/-!
The free-group step in the representation coding argument.  The topology on
homomorphisms is pointwise convergence, and this file applies to every
topological group, including the strong unitary group of a Hilbert space.
-/

namespace OperatorCoding

variable {ι G : Type*} [Group G]



/-- Conjugacy of group homomorphisms, by one fixed element of the target. -/
def RepresentationConjugate (ρ σ : FreeGroup ι →* G) : Prop :=
  ∃ w : G, ∀ g, w * ρ g * w⁻¹ = σ g

theorem lift_conjugate_iff (u v : ι → G) :
    RepresentationConjugate (FreeGroup.lift u) (FreeGroup.lift v) ↔
      TupleConjugate u v := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, fun i => by simpa using hw (FreeGroup.of i)⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, fun g => ?_⟩
    induction g using FreeGroup.induction_on with
    | C1 => simp
    | of i => simpa using hw i
    | inv_of i hi =>
      simpa [mul_assoc] using congrArg Inv.inv hi
    | mul a b ha hb =>
      simp only [map_mul]
      rw [← ha, ← hb]
      simp [mul_assoc]

theorem conjugate_iff_generators (ρ σ : FreeGroup ι →* G) :
    RepresentationConjugate ρ σ ↔
      TupleConjugate (fun i => ρ (FreeGroup.of i)) (fun i => σ (FreeGroup.of i)) := by
  simpa only [FreeGroup.lift.apply_symm_apply] using
    lift_conjugate_iff (FreeGroup.lift.symm ρ) (FreeGroup.lift.symm σ)

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]



theorem continuous_lift_evaluation (g : FreeGroup ι) :
    Continuous (fun u : ι → G => FreeGroup.lift u g) := by
  induction g using FreeGroup.induction_on with
  | C1 => simpa using (continuous_const : Continuous (fun _ : ι → G => (1 : G)))
  | of i => simpa using (continuous_apply i : Continuous (fun u : ι → G => u i))
  | inv_of i hi => simpa using hi.inv
  | mul a b ha hb => simpa using ha.mul hb

theorem continuous_lift : Continuous (FreeGroup.lift : (ι → G) → (FreeGroup ι →* G)) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi continuous_lift_evaluation

theorem continuous_generator_evaluation :
    Continuous (fun ρ : FreeGroup ι →* G => fun i => ρ (FreeGroup.of i)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (FreeGroup.of i)).comp continuous_induced_dom



end Topological

end OperatorCoding

end Source0

/- Preserved source skeleton: OperatorNormalization -/
section Source1
/-!
The normalization used before coding a bounded operator by two unitaries.
This file proves the normalization is reversible and exactly preserves
unitary equivalence.  It does not claim the spectral/exponential coding step.
-/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]



theorem operatorUnitaryEquivalent_norm {T S : H →L[ℂ] H}
    (h : OperatorUnitaryEquivalent T S) : ‖T‖ = ‖S‖ := by
  obtain ⟨u, hu⟩ := h
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg S)
    intro x
    calc
      ‖T x‖ = ‖u (T x)‖ := (u.norm_map _).symm
      _ = ‖S (u x)‖ := congrArg norm (hu x)
      _ ≤ ‖S‖ * ‖u x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖x‖ := by rw [u.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound S (norm_nonneg T)
    intro x
    obtain ⟨y, rfl⟩ := u.surjective x
    rw [← hu, u.norm_map, u.norm_map]
    exact T.le_opNorm _

noncomputable def normalizeOperator (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (((1 + ‖T‖)⁻¹ : ℝ) : ℂ) • T

theorem norm_normalizeOperator (T : H →L[ℂ] H) :
    ‖normalizeOperator T‖ = ‖T‖ / (1 + ‖T‖) := by
  have h : 0 < 1 + ‖T‖ := by positivity
  rw [normalizeOperator, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr h)]
  exact (div_eq_inv_mul _ _).symm

theorem norm_normalizeOperator_lt_one (T : H →L[ℂ] H) :
    ‖normalizeOperator T‖ < 1 := by
  rw [norm_normalizeOperator]
  apply (div_lt_one (by positivity : 0 < 1 + ‖T‖)).mpr
  linarith

theorem recover_normalizeOperator (T : H →L[ℂ] H) :
    ((((1 - ‖normalizeOperator T‖)⁻¹ : ℝ) : ℂ) • normalizeOperator T) = T := by
  have h : (1 + ‖T‖) ≠ 0 := ne_of_gt (by positivity)
  have hc : (1 - ‖T‖ / (1 + ‖T‖))⁻¹ * (1 + ‖T‖)⁻¹ = (1 : ℝ) := by
    field_simp
    <;> ring
  rw [norm_normalizeOperator, normalizeOperator, smul_smul, ← Complex.ofReal_mul,
    hc, Complex.ofReal_one, one_smul]



theorem normalizeOperator_unitaryEquivalent_iff (T S : H →L[ℂ] H) :
    OperatorUnitaryEquivalent (normalizeOperator T) (normalizeOperator S) ↔
      OperatorUnitaryEquivalent T S := by
  constructor
  · intro h
    have hn := operatorUnitaryEquivalent_norm h
    obtain ⟨u, hu⟩ := h
    refine ⟨u, fun x => ?_⟩
    have hux := congrArg (fun y : H => ((((1 - ‖normalizeOperator T‖)⁻¹ : ℝ) : ℂ) • y)) (hu x)
    dsimp only at hux
    rw [← u.map_smul] at hux
    have ht := congrArg (fun A : H →L[ℂ] H => A x) (recover_normalizeOperator T)
    have hs := congrArg (fun A : H →L[ℂ] H => A (u x)) (recover_normalizeOperator S)
    simp only [ContinuousLinearMap.smul_apply] at ht hs
    rw [ht, hn, hs] at hux
    exact hux
  · intro h
    have hn := operatorUnitaryEquivalent_norm h
    obtain ⟨u, hu⟩ := h
    refine ⟨u, fun x => ?_⟩
    simp only [normalizeOperator, ContinuousLinearMap.smul_apply, u.map_smul, hu, hn]

end OperatorCoding

end Source1

/- Preserved source skeleton: OperatorTargets -/
section Source2
/-!
Exact target propositions for Theorems 1.3 and 1.4 of MeasureEquivalence.tex.
These are definitions of the outstanding goals, not proofs of those goals.
The operator topology is strong convergence on vectors. Representations are
all group homomorphisms to the genuine strong unitary group.
-/

open MeasureTheory

namespace OperatorCoding

noncomputable section




abbrev UnitaryRepresentation (Γ : Type*) [Group Γ] := Γ →* StrongUnitary CanonicalHilbert





abbrev unitaryRepresentationTopology (Γ : Type*) [Group Γ] :
    TopologicalSpace (UnitaryRepresentation Γ) :=
  TopologicalSpace.induced
    (fun ρ : UnitaryRepresentation Γ => fun g : Γ => ρ g) inferInstance

abbrev unitaryRepresentationBorel (Γ : Type*) [Group Γ] :
    MeasurableSpace (UnitaryRepresentation Γ) :=
  @borel (UnitaryRepresentation Γ) (unitaryRepresentationTopology Γ)



def UnitaryRepresentationEquivalent {Γ : Type*} [Group Γ]
    (ρ σ : UnitaryRepresentation Γ) : Prop :=
  ∃ u : StrongUnitary CanonicalHilbert, ∀ g, u * ρ g * u⁻¹ = σ g







theorem borelReducesWith_trans {X Y Z : Type*}
    {mX : MeasurableSpace X} {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z}
    {E : X → X → Prop} {F : Y → Y → Prop} {G : Z → Z → Prop}
    (hEF : BorelReducesWith mX mY E F) (hFG : BorelReducesWith mY mZ F G) :
    BorelReducesWith mX mZ E G := by
  obtain ⟨f, hf, hE⟩ := hEF
  obtain ⟨g, hg, hF⟩ := hFG
  exact ⟨g ∘ f, @Measurable.comp X Y Z mX mY mZ g f hg hf,
    fun x y => (hE x y).trans (hF (f x) (f y))⟩





end
end OperatorCoding

end Source2

/- Preserved source skeleton: HilbertSequenceTopology -/
section Source3
/-! The canonical Hilbert space has its actual norm Polish topology;
its coordinate map is a measurable embedding for this topology. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace OperatorCoding

noncomputable section











theorem canonicalHilbert_coordinates_continuous :
    Continuous (fun x : CanonicalHilbert => (x : ℕ → ℂ)) := by
  apply continuous_pi
  intro i
  exact (lp.lipschitzWith_one_eval (E := fun _ : ℕ => ℂ) 2 i).continuous

theorem canonicalHilbert_coordinates_measurableEmbedding :
    @MeasurableEmbedding CanonicalHilbert (ℕ → ℂ) (borel CanonicalHilbert)
      inferInstance (fun x => (x : ℕ → ℂ)) := by
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  exact canonicalHilbert_coordinates_continuous.measurableEmbedding (fun _ _ h => lp.ext h)

end
end OperatorCoding

end Source3

/- Preserved source skeleton: OperatorBorelNormalization -/
section Source4
/-! The operator norm is lower semicontinuous in SOT, and the reversible
normalization T ↦ T/(1+‖T‖) is Borel for the correct strong Borel structure. -/

open Set MeasureTheory

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable abbrev operatorStrongTopologyOn : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun T : H →L[ℂ] H => fun x : H => T x) inferInstance

noncomputable abbrev operatorStrongBorel : MeasurableSpace (H →L[ℂ] H) :=
  @borel (H →L[ℂ] H) (operatorStrongTopologyOn H)

variable {H}

theorem operatorNorm_measurable :
    @Measurable (H →L[ℂ] H) ℝ (operatorStrongBorel H) inferInstance (fun T => ‖T‖) := by
  letI : TopologicalSpace (H →L[ℂ] H) := operatorStrongTopologyOn H
  letI : MeasurableSpace (H →L[ℂ] H) := operatorStrongBorel H
  letI : BorelSpace (H →L[ℂ] H) := ⟨rfl⟩
  change Measurable (fun T : H →L[ℂ] H => ‖T‖)
  have hlsc : LowerSemicontinuous (fun T : H →L[ℂ] H => ‖T‖) := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro r
    by_cases hr : 0 ≤ r
    · have hset : (fun T : H →L[ℂ] H => ‖T‖) ⁻¹' Iic r =
          ⋂ x : H, {T : H →L[ℂ] H | ‖T x‖ ≤ r * ‖x‖} := by
        ext T
        simp only [mem_preimage, mem_Iic, mem_iInter, mem_setOf_eq,
          ContinuousLinearMap.opNorm_le_iff hr]
      rw [hset]
      apply isClosed_iInter
      intro x
      have he : Continuous (fun T : H →L[ℂ] H => T x) :=
        (continuous_apply x).comp continuous_induced_dom
      exact isClosed_le he.norm continuous_const
    · have hset : (fun T : H →L[ℂ] H => ‖T‖) ⁻¹' Iic r = ∅ := by
        ext T
        simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
        exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge hr) (norm_nonneg T))
      rw [hset]
      exact isClosed_empty
  exact hlsc.measurable

theorem normalizeOperator_measurable :
    @Measurable (H →L[ℂ] H) (H →L[ℂ] H)
      (operatorStrongBorel H) (operatorStrongBorel H) normalizeOperator := by
  letI : TopologicalSpace (H →L[ℂ] H) := operatorStrongTopologyOn H
  letI : MeasurableSpace (H →L[ℂ] H) := operatorStrongBorel H
  letI : BorelSpace (H →L[ℂ] H) := ⟨rfl⟩
  have hn : Measurable (fun T : H →L[ℂ] H => ‖T‖) := operatorNorm_measurable
  have hc : Measurable (fun T : H →L[ℂ] H => (((1 + ‖T‖)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp ((measurable_const.add hn).inv)
  have hsmul : Continuous (fun p : ℂ × (H →L[ℂ] H) => p.1 • p.2) := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro x
    have he : Continuous (fun p : ℂ × (H →L[ℂ] H) => p.2 x) :=
      ((continuous_apply x).comp continuous_induced_dom).comp continuous_snd
    exact continuous_fst.smul he
  exact hsmul.measurable.comp (hc.prodMk measurable_id)

end OperatorCoding

end Source4

/- Preserved source skeleton: OperatorAdjointMeasurable -/
section Source5
/-! Adjoint evaluation is measurable for the strong Borel structure on
operators on the canonical separable Hilbert space. -/

namespace OperatorCoding

theorem canonical_adjoint_coordinate (T : CanonicalOperator) (x : CanonicalHilbert) (n : ℕ) :
    (T.adjoint x) n = inner ℂ (T (lp.single 2 n (1 : ℂ))) x := by
  simpa [lp.inner_single_left] using
    T.adjoint_inner_right (lp.single 2 n (1 : ℂ)) x

theorem canonical_adjoint_apply_measurable (x : CanonicalHilbert) :
    @Measurable CanonicalOperator CanonicalHilbert (operatorStrongBorel CanonicalHilbert)
      (borel CanonicalHilbert) (fun T => T.adjoint x) := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopologyOn CanonicalHilbert
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : BorelSpace CanonicalOperator := ⟨rfl⟩
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  apply canonicalHilbert_coordinates_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun T : CanonicalOperator => fun n : ℕ => (T.adjoint x) n)
  apply measurable_pi_iff.mpr
  intro n
  have he : Continuous (fun T : CanonicalOperator => T (lp.single 2 n (1 : ℂ))) :=
    (continuous_apply _).comp continuous_induced_dom
  have hi : Continuous (fun T : CanonicalOperator => inner ℂ (T (lp.single 2 n (1 : ℂ))) x) :=
    he.inner continuous_const
  simpa only [canonical_adjoint_coordinate] using hi.measurable

end OperatorCoding

end Source5

/- Preserved source skeleton: OperatorBlocks -/
section Source6
/-!
Concrete block operators on a countable Hilbert sum, for the tuple coding.
All blocks are actual bounded operators; the estimates below justify the
operator-norm convergence of the weighted series in the manuscript.
-/

open ContinuousLinearMap
open scoped ENNReal

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]



















variable [CompleteSpace H]

theorem blockOperator_adjoint (i j : ℕ) (A : H →L[ℂ] H) :
    (blockOperator i j A).adjoint = blockOperator j i A.adjoint := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [blockOperator_apply, blockOperator_apply, lp.inner_single_left, lp.inner_single_right]
  exact A.adjoint_inner_left _ _

end OperatorCoding

end Source6

/- Preserved source skeleton: OperatorSeries -/
section Source7
/-! The norm-convergent series of the countable unitary-tuple coding. -/

open ContinuousLinearMap

namespace OperatorCoding

set_option maxHeartbeats 1000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]















theorem starConnector_norm_le (n : ℕ) : ‖starConnector (H := H) n‖ ≤ 2 := by
  unfold starConnector
  exact (norm_add_le (identityBlock (H := H) 0 (n + 1)) (identityBlock (H := H) (n + 1) 0)).trans (by
    have h₁ := identityBlock_norm_le (H := H) 0 (n + 1)
    have h₂ := identityBlock_norm_le (H := H) (n + 1) 0
    linarith)

theorem unitaryCLM_norm_le (u : StrongUnitary H) : ‖(u : H →L[ℂ] H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using le_of_eq (u.norm_map x)



theorem tupleConnector_norm_le (u : ℕ → StrongUnitary H) (n : ℕ) :
    ‖tupleConnector u n‖ ≤ 2 := by
  unfold tupleConnector
  apply (norm_add_le (blockOperator (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H))
    (blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint)).trans
  have h₁ := (blockOperator_norm_le (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H)).trans
    (unitaryCLM_norm_le (u n))
  have h₂ : ‖blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint‖ ≤ 1 := by
    apply (blockOperator_norm_le _ _ _).trans
    simpa using unitaryCLM_norm_le (u n).symm
  linarith









theorem summable_starConnectors :
    Summable (fun n => weightedOperator (H := H) (1 / 32) n (starConnector n)) :=
  summable_weightedOperator starConnector_norm_le _

theorem summable_tupleConnectors (u : ℕ → StrongUnitary H) :
    Summable (fun n => weightedOperator (1 / 16) n (tupleConnector u n)) :=
  summable_weightedOperator (tupleConnector_norm_le u) _



end OperatorCoding

end Source7

/- Preserved source skeleton: OperatorCoefficients -/
section Source8
/-! Matrix entries of the actual norm-convergent operator coding. -/

open ContinuousLinearMap

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]





theorem weightedOperator_coordinate (c : ℝ) (n : ℕ)
    (A : HilbertSum H →L[ℂ] HilbertSum H) (x : HilbertSum H) (i : ℕ) :
    weightedOperator c n A x i = (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) • (A x i) := rfl

theorem starConnector_coordinate (n : ℕ) (x : HilbertSum H) (i : ℕ) :
    starConnector n x i = identityBlock 0 (n + 1) x i + identityBlock (n + 1) 0 x i := rfl

theorem tupleConnector_coordinate (u : ℕ → StrongUnitary H) (n : ℕ) (x : HilbertSum H) (i : ℕ) :
    tupleConnector u n x i =
      blockOperator (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H) x i +
      blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint x i := rfl





theorem tupleImaginaryPart_star_entry (u : ℕ → StrongUnitary H) (j : ℕ) (x : H) :
    tupleImaginaryPart u (lp.single 2 (j + 1) x) 0 =
      ((((1 / 32 : ℝ) * (1 / 2 : ℝ) ^ j : ℝ) : ℂ)) • x := by
  change operatorCoordinate (lp.single 2 (j + 1) x) 0 (tupleImaginaryPart u) = _
  rw [tupleImaginaryPart, map_add,
    (operatorCoordinate _ _).map_tsum summable_starConnectors,
    (operatorCoordinate _ _).map_tsum (summable_tupleConnectors u)]
  have hstar : (∑' n, operatorCoordinate (lp.single 2 (j + 1) x) 0
      (weightedOperator (1 / 32) n (starConnector n))) =
      ((((1 / 32 : ℝ) * (1 / 2 : ℝ) ^ j : ℝ) : ℂ)) • x := by
    rw [tsum_eq_single j]
    · simp [operatorCoordinate_apply, weightedOperator_coordinate, starConnector_coordinate, identityBlock,
        blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply]
    · intro n hnj
      simp [operatorCoordinate_apply, weightedOperator_coordinate, starConnector_coordinate, identityBlock,
        blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, Ne.symm hnj]
  rw [hstar]
  have hzero : (∑' n, operatorCoordinate (lp.single 2 (j + 1) x) 0
      (weightedOperator (1 / 16) n (tupleConnector u n))) = 0 := by
    apply Eq.trans (b := ∑' _ : ℕ, (0 : H))
    · apply tsum_congr
      intro n
      have h₁ : (0 : ℕ) ≠ 2 * n + 1 := by omega
      have h₂ : (0 : ℕ) ≠ 2 * n + 2 := by omega
      simp [operatorCoordinate_apply, weightedOperator_coordinate, tupleConnector_coordinate,
        blockOperator_coordinate, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, h₁, h₂]
    · simp
  rw [hzero, add_zero]

theorem tupleImaginaryPart_tuple_entry (u : ℕ → StrongUnitary H) (n : ℕ) (x : H) :
    tupleImaginaryPart u (lp.single 2 (2 * n + 2) x) (2 * n + 1) =
      ((((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ)) • u n x := by
  change operatorCoordinate (lp.single 2 (2 * n + 2) x) (2 * n + 1) (tupleImaginaryPart u) = _
  rw [tupleImaginaryPart, map_add,
    (operatorCoordinate _ _).map_tsum summable_starConnectors,
    (operatorCoordinate _ _).map_tsum (summable_tupleConnectors u)]
  have hzero : (∑' k, operatorCoordinate (lp.single 2 (2 * n + 2) x) (2 * n + 1)
      (weightedOperator (1 / 32) k (starConnector k))) = 0 := by
    apply Eq.trans (b := ∑' _ : ℕ, (0 : H))
    · apply tsum_congr
      intro k
      have h₁ : 2 * n + 1 ≠ 0 := by omega
      have h₂ : (0 : ℕ) ≠ 2 * n + 2 := by omega
      simp [operatorCoordinate_apply, weightedOperator_coordinate, starConnector_coordinate, identityBlock,
        blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, h₁, h₂]
    · simp
  rw [hzero, zero_add, tsum_eq_single n]
  · have h : 2 * n + 1 ≠ 2 * n + 2 := by omega
    simp [operatorCoordinate_apply, weightedOperator_coordinate, tupleConnector_coordinate,
      blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, h]
  · intro k hkn
    have h₁ : 2 * n + 1 ≠ 2 * k + 1 := by omega
    have h₂ : 2 * n + 1 ≠ 2 * k + 2 := by omega
    have h₃ : n ≠ k := Ne.symm hkn
    have h₄ : 2 * n ≠ 2 * k + 1 := by omega
    simp [operatorCoordinate_apply, weightedOperator_coordinate, tupleConnector_coordinate,
      blockOperator_coordinate, lp.single_apply, h₁, h₂, h₃, h₄]

end OperatorCoding

end Source8

/- Preserved source skeleton: OperatorAdjoints -/
section Source9
/-! Self-adjointness and the 7/8 norm bound in the tuple coding. -/

open ContinuousLinearMap
open scoped ENNReal

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



theorem identityBlock_star (i j : ℕ) : star (identityBlock (H := H) i j) = identityBlock j i := by
  simp only [identityBlock, ContinuousLinearMap.star_eq_adjoint, blockOperator_adjoint,
    ContinuousLinearMap.adjoint_id]

theorem starConnector_star (n : ℕ) : star (starConnector (H := H) n) = starConnector n := by
  simp [starConnector, star_add, identityBlock_star, add_comm]

theorem tupleConnector_star (u : ℕ → StrongUnitary H) (n : ℕ) :
    star (tupleConnector u n) = tupleConnector u n := by
  simp only [tupleConnector, star_add, ContinuousLinearMap.star_eq_adjoint,
    blockOperator_adjoint, ContinuousLinearMap.adjoint_adjoint, add_comm]

theorem weightedOperator_star (c : ℝ) (n : ℕ)
    (A : HilbertSum H →L[ℂ] HilbertSum H) :
    star (weightedOperator c n A) = weightedOperator c n (star A) := by
  simp [weightedOperator, star_smul]

theorem tupleDiagonal_star : star (tupleDiagonal (H := H)) = tupleDiagonal := by
  rw [tupleDiagonal, tsum_star]
  congr 1
  funext n
  rw [weightedOperator_star, identityBlock_star]

theorem tupleImaginaryPart_star (u : ℕ → StrongUnitary H) :
    star (tupleImaginaryPart u) = tupleImaginaryPart u := by
  unfold tupleImaginaryPart
  rw [star_add, tsum_star, tsum_star]
  congr 1 <;> congr 1 <;> funext n
  · rw [weightedOperator_star, starConnector_star]
  · rw [weightedOperator_star, tupleConnector_star]





end OperatorCoding

end Source9

/- Preserved source skeleton: OperatorAmplification -/
section Source10
/-! The direct sum of one unitary on every Hilbert summand. -/

namespace OperatorCoding

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



theorem amplifyUnitary_apply (W : StrongUnitary H) (x : HilbertSum H) (i : ℕ) :
    amplifyUnitary W x i = W (x i) := rfl



theorem amplifyUnitary_block_intertwines (W : StrongUnitary H) (i j : ℕ)
    (A B : H →L[ℂ] H) (hAB : ∀ x, W (A x) = B (W x)) (x : HilbertSum H) :
    amplifyUnitary W (blockOperator i j A x) = blockOperator i j B (amplifyUnitary W x) := by
  apply lp.ext
  funext k
  by_cases h : k = i
  · subst k
    simp [amplifyUnitary_apply, blockOperator_coordinate, hAB]
  · simp [amplifyUnitary_apply, blockOperator_coordinate, h]

end OperatorCoding

end Source10

/- Preserved source skeleton: OperatorConjugation -/
section Source11
/-! A unitary conjugacy of coded operators preserves the diagonal marker
and separately intertwines the self-adjoint tuple-coding component. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorUnitaryEquivalent_iff_conjugate (T S : H →L[ℂ] H) :
    OperatorUnitaryEquivalent T S ↔ ∃ Q : StrongUnitary H, Q.conjStarAlgEquiv T = S := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    ext x
    simpa using hQ (Q.symm x)
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun x => ?_⟩
    have h := congrArg (fun A : H →L[ℂ] H => A (Q x)) hQ
    simpa using h



theorem operatorRealPart_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (operatorRealPart T) = operatorRealPart (Q.conjStarAlgEquiv T) := by
  simp only [operatorRealPart, map_smul, map_add]
  exact congrArg (fun A : H →L[ℂ] H => (1 / 2 : ℂ) • (Q.conjStarAlgEquiv T + A))
    (Q.conjStarAlgEquiv.map_star' T)

theorem tupleCodedOperator_realPart (u : ℕ → StrongUnitary H) :
    operatorRealPart (tupleCodedOperator u) = tupleDiagonal := by
  simp only [operatorRealPart, tupleCodedOperator, star_add, star_smul, tupleDiagonal_star,
    tupleImaginaryPart_star, Complex.star_def, map_neg, Complex.conj_I]
  module

theorem codedOperator_conjugate_diagonal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    Q.conjStarAlgEquiv tupleDiagonal = tupleDiagonal := by
  calc
    Q.conjStarAlgEquiv tupleDiagonal =
        Q.conjStarAlgEquiv (operatorRealPart (tupleCodedOperator u)) := by
      rw [tupleCodedOperator_realPart]
    _ = operatorRealPart (Q.conjStarAlgEquiv (tupleCodedOperator u)) :=
      operatorRealPart_conjugate _ _
    _ = operatorRealPart (tupleCodedOperator v) := by rw [hQ]
    _ = tupleDiagonal := tupleCodedOperator_realPart v

theorem codedOperator_conjugate_imaginary (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    Q.conjStarAlgEquiv (tupleImaginaryPart u) = tupleImaginaryPart v := by
  have hd := codedOperator_conjugate_diagonal u v Q hQ
  have hi : Complex.I • Q.conjStarAlgEquiv (tupleImaginaryPart u) =
      Complex.I • tupleImaginaryPart v := by
    apply add_left_cancel (a := tupleDiagonal)
    simpa only [tupleCodedOperator, map_add, map_smul, hd] using hQ
  exact (smul_right_injective (HilbertSum H →L[ℂ] HilbertSum H)
    (by simp : Complex.I ≠ 0)) hi

theorem codedOperator_commutes_diagonal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x) := by
  intro x
  have h := congrArg (fun T : HilbertSum H →L[ℂ] HilbertSum H => T (Q x))
    (codedOperator_conjugate_diagonal u v Q hQ)
  simpa using h

end OperatorCoding

end Source11

/- Preserved source skeleton: OperatorPreservation -/
section Source12
/-! A simultaneous conjugacy of the tuple implements a conjugacy of the
single bounded operator by taking its direct sum on all summands. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryConjugate_tsum (Q : StrongUnitary H) (f : ℕ → H →L[ℂ] H) :
    Q.conjStarAlgEquiv (∑' n, f n) = ∑' n, Q.conjStarAlgEquiv (f n) := by
  exact Q.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv.map_tsum (f := f)

theorem amplifyUnitary_conjugates_block (W : StrongUnitary H) (i j : ℕ)
    (A B : H →L[ℂ] H) (hAB : ∀ x, W (A x) = B (W x)) :
    (amplifyUnitary W).conjStarAlgEquiv (blockOperator i j A) = blockOperator i j B := by
  apply ContinuousLinearMap.ext
  intro x
  simpa using amplifyUnitary_block_intertwines W i j A B hAB ((amplifyUnitary W).symm x)

theorem amplifyUnitary_conjugates_identityBlock (W : StrongUnitary H) (i j : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (identityBlock i j) = identityBlock i j := by
  apply amplifyUnitary_conjugates_block
  intro x
  rfl

theorem amplifyUnitary_conjugates_starConnector (W : StrongUnitary H) (n : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (starConnector n) = starConnector n := by
  simp only [starConnector, map_add, amplifyUnitary_conjugates_identityBlock]

theorem unitary_intertwines_inverse (W U V : StrongUnitary H)
    (h : ∀ x, W (U x) = V (W x)) : ∀ x, W (U.symm x) = V.symm (W x) := by
  intro x
  apply V.injective
  simpa using (h (U.symm x)).symm

theorem amplifyUnitary_conjugates_tupleConnector (W : StrongUnitary H)
    (u v : ℕ → StrongUnitary H) (h : ∀ n x, W (u n x) = v n (W x)) (n : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (tupleConnector u n) = tupleConnector v n := by
  unfold tupleConnector
  rw [map_add]
  congr 1
  · exact amplifyUnitary_conjugates_block W _ _ _ _ (h n)
  · apply amplifyUnitary_conjugates_block
    intro x
    simpa using unitary_intertwines_inverse W (u n) (v n) (h n) x

theorem amplifyUnitary_conjugates_diagonal (W : StrongUnitary H) :
    (amplifyUnitary W).conjStarAlgEquiv tupleDiagonal = tupleDiagonal := by
  unfold tupleDiagonal
  rw [unitaryConjugate_tsum]
  apply tsum_congr
  intro n
  simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_identityBlock]

theorem amplifyUnitary_conjugates_imaginary (W : StrongUnitary H)
    (u v : ℕ → StrongUnitary H) (h : ∀ n x, W (u n x) = v n (W x)) :
    (amplifyUnitary W).conjStarAlgEquiv (tupleImaginaryPart u) = tupleImaginaryPart v := by
  unfold tupleImaginaryPart
  rw [map_add, unitaryConjugate_tsum, unitaryConjugate_tsum]
  congr 1 <;> apply tsum_congr <;> intro n
  · simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_starConnector]
  · simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_tupleConnector W u v h]

theorem tupleCodedOperator_preserves (u v : ℕ → StrongUnitary H)
    (h : TupleConjugate u v) :
    OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v) := by
  obtain ⟨W, hW⟩ := h
  have hw : ∀ n x, W (u n x) = v n (W x) := by
    intro n x
    have hx := congrArg (fun U : StrongUnitary H => U (W x)) (hW n)
    simpa using hx
  apply (operatorUnitaryEquivalent_iff_conjugate _ _).mpr
  refine ⟨amplifyUnitary W, ?_⟩
  simp only [tupleCodedOperator, map_add, map_smul, amplifyUnitary_conjugates_diagonal,
    amplifyUnitary_conjugates_imaginary W u v hw]

end OperatorCoding

end Source12

/- Preserved source skeleton: OperatorEigenspaces -/
section Source13
/-! The diagonal marker separates all countably many Hilbert summands. -/

namespace OperatorCoding

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



























theorem commutingDiagonal_coordinate (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (x : HilbertSum H) (i : ℕ) :
    Q x i = diagonalRestriction Q i (x i) := by
  have hsum := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x
  have hcoord := ((hsum.mapL (Q : HilbertSum H →L[ℂ] HilbertSum H)).mapL
    (lp.evalCLM ℂ (fun _ : ℕ => H) 2 i)).tsum_eq
  change (∑' j, Q (lp.single 2 j (x j)) i) = Q x i at hcoord
  rw [← hcoord, tsum_eq_single i]
  · rfl
  · intro j hji
    rw [commutingDiagonal_single Q hQ j]
    simp [lp.single_apply, Ne.symm hji]

end OperatorCoding

end Source13

/- Preserved source skeleton: OperatorRecovery -/
section Source14
/-! Recovery of one simultaneous intertwiner from a conjugacy of the coded
bounded operators.  The star-shaped identity edges force all diagonal
unitaries to coincide, and the remaining edges recover every input unitary. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveGeometric_coefficient_ne_zero (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero hc (pow_ne_zero _ (by norm_num))

theorem conjugate_eq_intertwines (Q : StrongUnitary H) (T S : H →L[ℂ] H)
    (h : Q.conjStarAlgEquiv T = S) : ∀ x, Q (T x) = S (Q x) := by
  intro x
  have hx := congrArg (fun A : H →L[ℂ] H => A (Q x)) h
  simpa using hx

theorem coding_diagonalRestrictions_equal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hd : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x))
    (hb : ∀ x, Q (tupleImaginaryPart u x) = tupleImaginaryPart v (Q x))
    (j : ℕ) (x : H) : diagonalRestriction Q j x = diagonalRestriction Q 0 x := by
  cases j with
  | zero => rfl
  | succ j =>
    have h := congrArg (fun z : HilbertSum H => z 0) (hb (lp.single 2 (j + 1) x))
    dsimp only at h
    rw [commutingDiagonal_coordinate Q hd, tupleImaginaryPart_star_entry,
      commutingDiagonal_single Q hd, tupleImaginaryPart_star_entry,
      (diagonalRestriction Q 0).map_smul] at h
    exact ((smul_right_injective H
      (positiveGeometric_coefficient_ne_zero (1 / 32) (by norm_num) j)) h).symm

theorem coding_recovered_intertwiner (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hd : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x))
    (hb : ∀ x, Q (tupleImaginaryPart u x) = tupleImaginaryPart v (Q x))
    (n : ℕ) (x : H) :
    diagonalRestriction Q 0 (u n x) = v n (diagonalRestriction Q 0 x) := by
  have h := congrArg (fun z : HilbertSum H => z (2 * n + 1))
    (hb (lp.single 2 (2 * n + 2) x))
  dsimp only at h
  rw [commutingDiagonal_coordinate Q hd, tupleImaginaryPart_tuple_entry,
    commutingDiagonal_single Q hd, tupleImaginaryPart_tuple_entry,
    (diagonalRestriction Q (2 * n + 1)).map_smul] at h
  rw [coding_diagonalRestrictions_equal u v Q hd hb (2 * n + 1),
    coding_diagonalRestrictions_equal u v Q hd hb (2 * n + 2)] at h
  exact (smul_right_injective H
    (positiveGeometric_coefficient_ne_zero (1 / 16) (by norm_num) n)) h

theorem tupleCodedOperator_reflects (u v : ℕ → StrongUnitary H)
    (h : OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v)) :
    TupleConjugate u v := by
  obtain ⟨Q, hQ⟩ := (operatorUnitaryEquivalent_iff_conjugate _ _).mp h
  have hd := codedOperator_commutes_diagonal u v Q hQ
  have hb := conjugate_eq_intertwines Q _ _ (codedOperator_conjugate_imaginary u v Q hQ)
  let W := diagonalBlockUnitary Q hd 0
  refine ⟨W, fun n => ?_⟩
  apply LinearIsometryEquiv.ext
  intro x
  have hx := coding_recovered_intertwiner u v Q hd hb n (W.symm x)
  change W (u n (W.symm x)) = v n (W (W.symm x)) at hx
  simpa using hx

end OperatorCoding

end Source14

/- Preserved source skeleton: OperatorTupleCoding -/
section Source15
/-!
The manuscript's explicit continuous reduction from simultaneous unitary
equivalence of countable tuples to unitary equivalence of a single operator.
The target is the actual countable Hilbert sum, with the strong operator
topology, and the resulting operators have norm at most 7/8.
-/

open ContinuousLinearMap

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tupleConnector_continuous_apply (n : ℕ) (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleConnector u n x) := by
  have h₁ : Continuous (fun u : ℕ → StrongUnitary H => u n (x (2 * n + 2))) :=
    (strongUnitary_continuous_eval _).comp (continuous_apply n)
  have h₂ : Continuous (fun u : ℕ → StrongUnitary H => (u n).symm (x (2 * n + 1))) :=
    (strongUnitary_continuous_eval _).comp (continuous_apply n).inv
  have hs₁ := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 (2 * n + 1)).continuous.comp h₁
  have hs₂ := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 (2 * n + 2)).continuous.comp h₂
  simpa only [tupleConnector, ContinuousLinearMap.add_apply, blockOperator_apply,
    LinearIsometryEquiv.adjoint_eq_symm, lp.singleContinuousLinearMap_apply] using hs₁.add hs₂

theorem weightedTupleConnector_continuous_apply (n : ℕ) (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => weightedOperator (1 / 16) n (tupleConnector u n) x) := by
  exact (tupleConnector_continuous_apply n x).const_smul
    ((((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ))

theorem weightedTupleConnector_norm_bound (n : ℕ) (u : ℕ → StrongUnitary H) (x : HilbertSum H) :
    ‖weightedOperator (1 / 16) n (tupleConnector u n) x‖ ≤
      (‖x‖ / 8) * (1 / 2 : ℝ) ^ n := by
  have hb := weightedOperator_norm_le (tupleConnector_norm_le u) (1 / 16) n
  norm_num at hb
  calc
    ‖weightedOperator (1 / 16) n (tupleConnector u n) x‖ ≤
        ‖weightedOperator (1 / 16) n (tupleConnector u n)‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((1 / 8 : ℝ) * (1 / 2 : ℝ) ^ n) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg x)
    _ = (‖x‖ / 8) * (1 / 2 : ℝ) ^ n := by ring

theorem tupleImaginaryPart_continuous_apply (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleImaginaryPart u x) := by
  have hsum : Continuous (fun u : ℕ → StrongUnitary H =>
      ∑' n, weightedOperator (1 / 16) n (tupleConnector u n) x) := by
    apply continuous_tsum (fun n => weightedTupleConnector_continuous_apply n x)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (‖x‖ / 8))
    exact fun n u => weightedTupleConnector_norm_bound n u x
  have hconst : Continuous (fun _ : ℕ → StrongUnitary H =>
    (∑' n, weightedOperator (H := H) (1 / 32) n (starConnector n)) x) := continuous_const
  convert hconst.add hsum using 1
  funext u
  rw [tupleImaginaryPart, ContinuousLinearMap.add_apply]
  congr 1
  exact (ContinuousLinearMap.apply ℂ (HilbertSum H) x).map_tsum (summable_tupleConnectors u)

theorem tupleCodedOperator_continuous_apply (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleCodedOperator u x) := by
  exact continuous_const.add ((tupleImaginaryPart_continuous_apply x).const_smul Complex.I)





theorem tupleCodedOperator_equivalent_iff (u v : ℕ → StrongUnitary H) :
    OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v) ↔
      TupleConjugate u v :=
  ⟨tupleCodedOperator_reflects u v, tupleCodedOperator_preserves u v⟩



end OperatorCoding

end Source15

/- Preserved source skeleton: OperatorPairCoding -/
section Source16
/-! Coding an arbitrary bounded operator by two unitaries using normalized
real and imaginary parts and the exponential on the self-adjoint π-ball. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def conjugateSelfAdjoint (Q : StrongUnitary H)
    (a : selfAdjoint (H →L[ℂ] H)) : selfAdjoint (H →L[ℂ] H) :=
  ⟨Q.conjStarAlgEquiv a, a.property.map Q.conjStarAlgEquiv⟩

theorem conjugateSelfAdjoint_norm (Q : StrongUnitary H) (a : selfAdjoint (H →L[ℂ] H)) :
    ‖conjugateSelfAdjoint Q a‖ = ‖a‖ := by
  change ‖Q.conjStarAlgEquiv (a : H →L[ℂ] H)‖ = ‖(a : H →L[ℂ] H)‖
  exact StarAlgEquiv.norm_map Q.conjStarAlgEquiv (a : H →L[ℂ] H)

theorem expUnitary_conjugate (Q : StrongUnitary H) (a : selfAdjoint (H →L[ℂ] H)) :
    Q.conjStarAlgEquiv (selfAdjoint.expUnitary a : H →L[ℂ] H) =
      (selfAdjoint.expUnitary (conjugateSelfAdjoint Q a) : H →L[ℂ] H) := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  simp only [selfAdjoint.expUnitary_coe]
  rw [NormedSpace.map_exp Q.conjStarAlgEquiv (StarAlgEquiv.isometry Q.conjStarAlgEquiv).continuous,
    map_smul]
  rfl

theorem expUnitary_injective_pi_ball (a b : selfAdjoint (H →L[ℂ] H))
    (ha : ‖a‖ < Real.pi) (hb : ‖b‖ < Real.pi)
    (h : (selfAdjoint.expUnitary a : H →L[ℂ] H) = (selfAdjoint.expUnitary b : H →L[ℂ] H)) :
    a = b := by
  have hu : selfAdjoint.expUnitary a = selfAdjoint.expUnitary b := Subtype.ext h
  have hh := congrArg Unitary.argSelfAdjoint hu
  simpa only [argSelfAdjoint_expUnitary ha, argSelfAdjoint_expUnitary hb] using hh

theorem expUnitary_conjugate_reflects (Q : StrongUnitary H)
    (a b : selfAdjoint (H →L[ℂ] H)) (ha : ‖a‖ < Real.pi) (hb : ‖b‖ < Real.pi)
    (h : Q.conjStarAlgEquiv (selfAdjoint.expUnitary a : H →L[ℂ] H) =
      (selfAdjoint.expUnitary b : H →L[ℂ] H)) :
    Q.conjStarAlgEquiv (a : H →L[ℂ] H) = (b : H →L[ℂ] H) := by
  rw [expUnitary_conjugate] at h
  exact congrArg (fun c : selfAdjoint (H →L[ℂ] H) => (c : H →L[ℂ] H))
    (expUnitary_injective_pi_ball _ _ (by rw [conjugateSelfAdjoint_norm]; exact ha) hb h)

theorem conjugateUnitary_iff (Q U V : StrongUnitary H) :
    Q * U * Q⁻¹ = V ↔ Q.conjStarAlgEquiv (U : H →L[ℂ] H) = (V : H →L[ℂ] H) := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun W : StrongUnitary H => W x) h
  · intro h
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun T : H →L[ℂ] H => T x) h

noncomputable def normalizedRealPart (T : H →L[ℂ] H) : selfAdjoint (H →L[ℂ] H) :=
  realPart (normalizeOperator T)

noncomputable def normalizedImaginaryPart (T : H →L[ℂ] H) : selfAdjoint (H →L[ℂ] H) :=
  imaginaryPart (normalizeOperator T)

theorem normalizedRealPart_norm_lt_pi (T : H →L[ℂ] H) : ‖normalizedRealPart T‖ < Real.pi := by
  have h := (realPart.norm_le (normalizeOperator T)).trans_lt (norm_normalizeOperator_lt_one T)
  exact h.trans (by have hp := Real.two_le_pi; linarith)

theorem normalizedImaginaryPart_norm_lt_pi (T : H →L[ℂ] H) :
    ‖normalizedImaginaryPart T‖ < Real.pi := by
  have h := (imaginaryPart.norm_le (normalizeOperator T)).trans_lt (norm_normalizeOperator_lt_one T)
  exact h.trans (by have hp := Real.two_le_pi; linarith)

noncomputable def operatorUnitaryPair (T : H →L[ℂ] H) : Bool → StrongUnitary H
  | false => Unitary.linearIsometryEquiv (selfAdjoint.expUnitary (normalizedRealPart T))
  | true => Unitary.linearIsometryEquiv (selfAdjoint.expUnitary (normalizedImaginaryPart T))

theorem normalizeOperator_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (normalizeOperator T) = normalizeOperator (Q.conjStarAlgEquiv T) := by
  simp only [normalizeOperator, map_smul, StarAlgEquiv.norm_map]

theorem realPart_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (realPart T : H →L[ℂ] H) = (realPart (Q.conjStarAlgEquiv T) : H →L[ℂ] H) := by
  simp only [realPart_apply_coe, ← Complex.coe_smul, map_smul, map_add]
  exact congrArg (fun A : H →L[ℂ] H => ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) • (Q.conjStarAlgEquiv T + A))
    (Q.conjStarAlgEquiv.map_star' T)

theorem imaginaryPart_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (imaginaryPart T : H →L[ℂ] H) =
      (imaginaryPart (Q.conjStarAlgEquiv T) : H →L[ℂ] H) := by
  simp only [imaginaryPart_apply_coe, ← Complex.coe_smul, map_smul, map_sub]
  exact congrArg (fun A : H →L[ℂ] H => -Complex.I • ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) • (Q.conjStarAlgEquiv T - A))
    (Q.conjStarAlgEquiv.map_star' T)

theorem operatorUnitaryPair_reflects (T S : H →L[ℂ] H)
    (h : TupleConjugate (operatorUnitaryPair T) (operatorUnitaryPair S)) :
    OperatorUnitaryEquivalent T S := by
  obtain ⟨Q, hQ⟩ := h
  have hr : Q.conjStarAlgEquiv (normalizedRealPart T : H →L[ℂ] H) = normalizedRealPart S := by
    apply expUnitary_conjugate_reflects Q _ _ (normalizedRealPart_norm_lt_pi T)
      (normalizedRealPart_norm_lt_pi S)
    simpa [operatorUnitaryPair] using (conjugateUnitary_iff Q _ _).mp (hQ false)
  have hi : Q.conjStarAlgEquiv (normalizedImaginaryPart T : H →L[ℂ] H) = normalizedImaginaryPart S := by
    apply expUnitary_conjugate_reflects Q _ _ (normalizedImaginaryPart_norm_lt_pi T)
      (normalizedImaginaryPart_norm_lt_pi S)
    simpa [operatorUnitaryPair] using (conjugateUnitary_iff Q _ _).mp (hQ true)
  apply (normalizeOperator_unitaryEquivalent_iff T S).mp
  apply (operatorUnitaryEquivalent_iff_conjugate _ _).mpr
  refine ⟨Q, ?_⟩
  calc
    Q.conjStarAlgEquiv (normalizeOperator T) =
        Q.conjStarAlgEquiv ((normalizedRealPart T : H →L[ℂ] H) +
          Complex.I • (normalizedImaginaryPart T : H →L[ℂ] H)) := by
      rw [normalizedRealPart, normalizedImaginaryPart, realPart_add_I_smul_imaginaryPart]
    _ = (normalizedRealPart S : H →L[ℂ] H) +
        Complex.I • (normalizedImaginaryPart S : H →L[ℂ] H) := by rw [map_add, map_smul, hr, hi]
    _ = normalizeOperator S := realPart_add_I_smul_imaginaryPart _

theorem operatorUnitaryPair_preserves (T S : H →L[ℂ] H) (h : OperatorUnitaryEquivalent T S) :
    TupleConjugate (operatorUnitaryPair T) (operatorUnitaryPair S) := by
  obtain ⟨Q, hQ⟩ := (operatorUnitaryEquivalent_iff_conjugate T S).mp h
  have hn : Q.conjStarAlgEquiv (normalizeOperator T) = normalizeOperator S := by
    rw [normalizeOperator_conjugate, hQ]
  have hr : conjugateSelfAdjoint Q (normalizedRealPart T) = normalizedRealPart S := by
    apply Subtype.ext
    change Q.conjStarAlgEquiv (realPart (normalizeOperator T) : H →L[ℂ] H) = _
    rw [realPart_conjugate, hn]
    rfl
  have hi : conjugateSelfAdjoint Q (normalizedImaginaryPart T) = normalizedImaginaryPart S := by
    apply Subtype.ext
    change Q.conjStarAlgEquiv (imaginaryPart (normalizeOperator T) : H →L[ℂ] H) = _
    rw [imaginaryPart_conjugate, hn]
    rfl
  refine ⟨Q, fun i => ?_⟩
  apply (conjugateUnitary_iff Q _ _).mpr
  cases i
  · simpa [operatorUnitaryPair, expUnitary_conjugate, hr] using expUnitary_conjugate Q (normalizedRealPart T)
  · simpa [operatorUnitaryPair, expUnitary_conjugate, hi] using expUnitary_conjugate Q (normalizedImaginaryPart T)

theorem operatorUnitaryPair_equivalent_iff (T S : H →L[ℂ] H) :
    TupleConjugate (operatorUnitaryPair T) (operatorUnitaryPair S) ↔ OperatorUnitaryEquivalent T S :=
  ⟨operatorUnitaryPair_reflects T S, operatorUnitaryPair_preserves T S⟩

end OperatorCoding

end Source16

/- Preserved source skeleton: OperatorMeasurableEvaluation -/
section Source17
/-! Borel vector evaluations of the exponential-pair operator coding. -/

open Filter Topology MeasureTheory ContinuousLinearMap

namespace OperatorCoding

section General

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace X]

theorem measurable_operator_action {A : X → H →L[ℂ] H}
    (hA : ∀ v : H, Measurable (fun a => A a v)) {x : X → H} (hx : Measurable x) :
    Measurable (fun a => A a (x a)) := by
  have huncurry := measurable_uncurry_of_continuous_of_measurable
    (u := fun v : H => fun a : X => A a v) (fun a => (A a).continuous) hA
  exact huncurry.comp (hx.prodMk measurable_id)

theorem measurable_operator_pow_apply {A : X → H →L[ℂ] H}
    (hA : ∀ v : H, Measurable (fun a => A a v)) (n : ℕ) (v : H) :
    Measurable (fun a => ((A a) ^ n) v) := by
  induction n with
  | zero => simpa using (measurable_const (a := v) : Measurable (fun _ : X => v))
  | succ n ih =>
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using measurable_operator_action hA ih

theorem measurable_operator_exp_apply {A : X → H →L[ℂ] H}
    (hA : ∀ v : H, Measurable (fun a => A a v)) (v : H) :
    Measurable (fun a => NormedSpace.exp (A a) v) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n a => ∑ k ∈ Finset.range n, ((k.factorial : ℂ)⁻¹) • (((A a) ^ k) v))
  · intro n
    exact (Finset.range n).measurable_sum (fun k _ =>
      (measurable_operator_pow_apply hA k v).const_smul ((k.factorial : ℂ)⁻¹))
  · apply tendsto_pi_nhds.mpr
    intro a
    exact ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (A a)).mapL
      (ContinuousLinearMap.apply ℂ H v)).tendsto_sum_nat

end General

theorem operatorStrong_apply_measurable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : H) : @Measurable (H →L[ℂ] H) H (operatorStrongBorel H) (borel H) (fun T => T x) := by
  letI : TopologicalSpace (H →L[ℂ] H) := operatorStrongTopologyOn H
  letI : MeasurableSpace (H →L[ℂ] H) := operatorStrongBorel H
  letI : BorelSpace (H →L[ℂ] H) := ⟨rfl⟩
  letI : MeasurableSpace H := borel H
  letI : BorelSpace H := ⟨rfl⟩
  have he : Continuous (fun T : H →L[ℂ] H => T x) :=
    (continuous_apply x).comp continuous_induced_dom
  exact he.measurable

theorem normalizedRealPart_apply_measurable (x : CanonicalHilbert) :
    @Measurable CanonicalOperator CanonicalHilbert (operatorStrongBorel CanonicalHilbert)
      (borel CanonicalHilbert) (fun T => (normalizedRealPart T : CanonicalOperator) x) := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  have hN := (operatorStrong_apply_measurable x).comp normalizeOperator_measurable
  have hD := (canonical_adjoint_apply_measurable x).comp normalizeOperator_measurable
  simpa only [normalizedRealPart, realPart_apply_coe, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.star_eq_adjoint] using
    (hN.add hD).const_smul ((2 : ℝ)⁻¹)

theorem normalizedImaginaryPart_apply_measurable (x : CanonicalHilbert) :
    @Measurable CanonicalOperator CanonicalHilbert (operatorStrongBorel CanonicalHilbert)
      (borel CanonicalHilbert) (fun T => (normalizedImaginaryPart T : CanonicalOperator) x) := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  have hN := (operatorStrong_apply_measurable x).comp normalizeOperator_measurable
  have hD := (canonical_adjoint_apply_measurable x).comp normalizeOperator_measurable
  simpa only [normalizedImaginaryPart, imaginaryPart_apply_coe, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.star_eq_adjoint] using
    ((hN.sub hD).const_smul ((2 : ℝ)⁻¹)).const_smul (-Complex.I)

theorem operatorUnitaryPair_apply_measurable (i : Bool) (x : CanonicalHilbert) :
    @Measurable CanonicalOperator CanonicalHilbert (operatorStrongBorel CanonicalHilbert)
      (borel CanonicalHilbert) (fun T => operatorUnitaryPair T i x) := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  cases i
  · have hA : ∀ v : CanonicalHilbert, Measurable (fun T : CanonicalOperator =>
        (Complex.I • (normalizedRealPart T : CanonicalOperator)) v) := by
      intro v
      exact (normalizedRealPart_apply_measurable v).const_smul Complex.I
    simpa only [operatorUnitaryPair, Unitary.coe_linearIsometryEquiv_apply,
      selfAdjoint.expUnitary_coe] using measurable_operator_exp_apply hA x
  · have hA : ∀ v : CanonicalHilbert, Measurable (fun T : CanonicalOperator =>
        (Complex.I • (normalizedImaginaryPart T : CanonicalOperator)) v) := by
      intro v
      exact (normalizedImaginaryPart_apply_measurable v).const_smul Complex.I
    simpa only [operatorUnitaryPair, Unitary.coe_linearIsometryEquiv_apply,
      selfAdjoint.expUnitary_coe] using measurable_operator_exp_apply hA x

end OperatorCoding

end Source17

/- Preserved source skeleton: OperatorUnitaryBorel -/
section Source18
/-! The strong topology on the unitary group is determined by countably
many dense vector evaluations. This identifies its Borel structure without
using operator-norm measurability in place of strong measurability. -/

open Filter Topology TopologicalSpace

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]



variable {H}







theorem strongUnitary_measurable_of_evaluations {X : Type*} [MeasurableSpace X]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : X → StrongUnitary H) (hf : ∀ x : H, Measurable (fun a => f a x)) :
    @Measurable X (StrongUnitary H) inferInstance (borel (StrongUnitary H)) f := by
  apply measurable_iff_comap_le.mpr
  change (borel (StrongUnitary H)).comap f ≤ (inferInstance : MeasurableSpace X)
  rw [strongUnitary_topology_eq_dense, borel_comap]
  rw [MeasurableSpace.comap_comp]
  have hb : (inferInstance : MeasurableSpace (ℕ → H)) = borel (ℕ → H) := BorelSpace.measurable_eq
  rw [← hb]
  exact measurable_iff_comap_le.mp (measurable_pi_iff.mpr (fun n => hf (denseSeq H n)))

theorem operatorUnitaryPair_measurable (i : Bool) :
    @Measurable CanonicalOperator (StrongUnitary CanonicalHilbert)
      (operatorStrongBorel CanonicalHilbert) (borel (StrongUnitary CanonicalHilbert))
      (fun T => operatorUnitaryPair T i) := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  exact strongUnitary_measurable_of_evaluations _ (fun x => operatorUnitaryPair_apply_measurable i x)

end OperatorCoding

end Source18

/- Preserved source skeleton: OperatorFreeRepresentation -/
section Source19
/-! The actual Borel reduction from all bounded operators to all unitary
representations of the countably generated free group. -/

namespace OperatorCoding

def padUnitaryPair {G : Type*} [Group G] (p : Bool → G) (n : ℕ) : G :=
  if n = 0 then p false else if n = 1 then p true else 1

theorem padUnitaryPair_conjugate_iff {G : Type*} [Group G] (p q : Bool → G) :
    TupleConjugate (padUnitaryPair p) (padUnitaryPair q) ↔ TupleConjugate p q := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W, fun i => ?_⟩
    cases i
    · simpa [padUnitaryPair] using hW 0
    · simpa [padUnitaryPair] using hW 1
  · rintro ⟨W, hW⟩
    refine ⟨W, fun n => ?_⟩
    by_cases h₀ : n = 0
    · simpa [padUnitaryPair, h₀] using hW false
    by_cases h₁ : n = 1
    · simpa [padUnitaryPair, h₀, h₁] using hW true
    · simp [padUnitaryPair, h₀, h₁]

noncomputable def operatorUnitarySequence (T : CanonicalOperator) : ℕ → StrongUnitary CanonicalHilbert :=
  padUnitaryPair (operatorUnitaryPair T)

theorem operatorUnitarySequence_equivalent_iff (T S : CanonicalOperator) :
    TupleConjugate (operatorUnitarySequence T) (operatorUnitarySequence S) ↔ OperatorUnitaryEquivalent T S :=
  (padUnitaryPair_conjugate_iff _ _).trans (operatorUnitaryPair_equivalent_iff T S)

theorem operatorUnitarySequence_measurable :
    @Measurable CanonicalOperator (ℕ → StrongUnitary CanonicalHilbert)
      (operatorStrongBorel CanonicalHilbert) (borel (ℕ → StrongUnitary CanonicalHilbert))
      operatorUnitarySequence := by
  letI : MeasurableSpace CanonicalOperator := operatorStrongBorel CanonicalHilbert
  letI : MeasurableSpace (StrongUnitary CanonicalHilbert) := borel (StrongUnitary CanonicalHilbert)
  letI : BorelSpace (StrongUnitary CanonicalHilbert) := ⟨rfl⟩
  have hb : (inferInstance : MeasurableSpace (ℕ → StrongUnitary CanonicalHilbert)) =
      borel (ℕ → StrongUnitary CanonicalHilbert) := BorelSpace.measurable_eq
  rw [← hb]
  apply measurable_pi_iff.mpr
  intro n
  by_cases h₀ : n = 0
  · simpa [operatorUnitarySequence, padUnitaryPair, h₀] using operatorUnitaryPair_measurable false
  by_cases h₁ : n = 1
  · simpa [operatorUnitarySequence, padUnitaryPair, h₀, h₁] using operatorUnitaryPair_measurable true
  · simp only [operatorUnitarySequence, padUnitaryPair, if_neg h₀, if_neg h₁]
    exact measurable_const

noncomputable def operatorFreeRepresentation (T : CanonicalOperator) :
    UnitaryRepresentation (FreeGroup ℕ) := FreeGroup.lift (operatorUnitarySequence T)

theorem operatorFreeRepresentation_measurable :
    @Measurable CanonicalOperator (UnitaryRepresentation (FreeGroup ℕ))
      (operatorStrongBorel CanonicalHilbert) (unitaryRepresentationBorel (FreeGroup ℕ))
      operatorFreeRepresentation := by
  have hLift := (continuous_lift (G := StrongUnitary CanonicalHilbert) (ι := ℕ)).borel_measurable
  exact hLift.comp operatorUnitarySequence_measurable

theorem operatorFreeRepresentation_equivalent_iff (T S : CanonicalOperator) :
    UnitaryRepresentationEquivalent (operatorFreeRepresentation T) (operatorFreeRepresentation S) ↔
      OperatorUnitaryEquivalent T S :=
  (lift_conjugate_iff _ _).trans (operatorUnitarySequence_equivalent_iff T S)

theorem boundedOperators_borelReduce_freeRepresentations :
    BorelReducesWith operatorBorel (unitaryRepresentationBorel (FreeGroup ℕ))
      OperatorUnitaryEquivalent UnitaryRepresentationEquivalent :=
  ⟨operatorFreeRepresentation, operatorFreeRepresentation_measurable,
    fun T S => (operatorFreeRepresentation_equivalent_iff T S).symm⟩

end OperatorCoding

end Source19

/- Preserved source skeleton: OperatorBireduction -/
section Source20
/-!
The right-hand Borel bireducibility in Theorem 1.4:
all unitary representations of F∞ and all bounded operators on the same
fixed canonical separable infinite-dimensional Hilbert space.
-/

namespace OperatorCoding

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem fixedHilbertConjugation_equivalent_iff (E : H ≃ₗᵢ[ℂ] K) (T S : H →L[ℂ] H) :
    OperatorUnitaryEquivalent (E.conjStarAlgEquiv T) (E.conjStarAlgEquiv S) ↔
      OperatorUnitaryEquivalent T S := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨(E.trans Q).trans E.symm, fun x => ?_⟩
    apply E.injective
    simpa using hQ (E x)
  · rintro ⟨Q, hQ⟩
    refine ⟨(E.symm.trans Q).trans E, fun x => ?_⟩
    simpa using congrArg E (hQ (E.symm x))



theorem canonicalTupleCodedOperator_equivalent_iff (u v : ℕ → StrongUnitary CanonicalHilbert) :
    OperatorUnitaryEquivalent (canonicalTupleCodedOperator u) (canonicalTupleCodedOperator v) ↔
      TupleConjugate u v :=
  (fixedHilbertConjugation_equivalent_iff _ _ _).trans (tupleCodedOperator_equivalent_iff u v)



theorem canonicalTupleCodedOperator_continuous :
    @Continuous (ℕ → StrongUnitary CanonicalHilbert) CanonicalOperator
      inferInstance operatorStrongTopology canonicalTupleCodedOperator := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  exact canonicalHilbertSumEquiv.continuous.comp
    (tupleCodedOperator_continuous_apply (canonicalHilbertSumEquiv.symm x))

noncomputable def freeRepresentationCodedOperator (ρ : UnitaryRepresentation (FreeGroup ℕ)) :
    CanonicalOperator := canonicalTupleCodedOperator (fun n => ρ (FreeGroup.of n))

theorem freeRepresentationCodedOperator_continuous :
    @Continuous (UnitaryRepresentation (FreeGroup ℕ)) CanonicalOperator
      (unitaryRepresentationTopology (FreeGroup ℕ)) operatorStrongTopology
      freeRepresentationCodedOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  exact canonicalTupleCodedOperator_continuous.comp continuous_generator_evaluation

theorem freeRepresentationCodedOperator_equivalent_iff
    (ρ σ : UnitaryRepresentation (FreeGroup ℕ)) :
    OperatorUnitaryEquivalent (freeRepresentationCodedOperator ρ) (freeRepresentationCodedOperator σ) ↔
      UnitaryRepresentationEquivalent ρ σ :=
  (canonicalTupleCodedOperator_equivalent_iff _ _).trans (conjugate_iff_generators ρ σ).symm

theorem freeRepresentations_borelReduce_boundedOperators :
    BorelReducesWith (unitaryRepresentationBorel (FreeGroup ℕ)) operatorBorel
      UnitaryRepresentationEquivalent OperatorUnitaryEquivalent := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  exact ⟨freeRepresentationCodedOperator, freeRepresentationCodedOperator_continuous.borel_measurable,
    fun ρ σ => (freeRepresentationCodedOperator_equivalent_iff ρ σ).symm⟩



end OperatorCoding

end Source20

/- Preserved source skeleton: BenchmarkOperatorTransport -/
section Source21
open MeasureTheory

noncomputable section

namespace BenchmarkComparisons

def representationToHom {Γ : Type*} [Group Γ] (ρ : Representation Γ) :
    OperatorCoding.UnitaryRepresentation Γ where
  toFun := ρ.operator
  map_one' := by apply LinearIsometryEquiv.ext; intro v; exact ρ.map_one v
  map_mul' := by intro g h; apply LinearIsometryEquiv.ext; intro v; exact ρ.map_mul g h v

def representationFromHom {Γ : Type*} [Group Γ] (ρ : OperatorCoding.UnitaryRepresentation Γ) :
    Representation Γ where
  operator := ρ
  map_one := by intro v; simp
  map_mul := by intro g h v; simp

def representationEquiv (Γ : Type*) [Group Γ] :
    Representation Γ ≃ OperatorCoding.UnitaryRepresentation Γ where
  toFun := representationToHom
  invFun := representationFromHom
  left_inv := by intro ρ; cases ρ; rfl
  right_inv := by intro ρ; ext g v; rfl

theorem continuous_representationToHom (Γ : Type*) [Group Γ] :
    @Continuous (Representation Γ) (OperatorCoding.UnitaryRepresentation Γ)
      (representationStrongTopology Γ) (OperatorCoding.unitaryRepresentationTopology Γ)
      representationToHom := by
  letI : TopologicalSpace (Representation Γ) := representationStrongTopology Γ
  letI : TopologicalSpace (OperatorCoding.UnitaryRepresentation Γ) :=
    OperatorCoding.unitaryRepresentationTopology Γ
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro g
  apply (OperatorCoding.strongUnitary_continuous_iff _).mpr
  intro v
  have hc : Continuous (fun ρ : Representation Γ => fun g : Γ => fun v : Hilbert => ρ.operator g v) :=
    continuous_induced_dom
  exact (continuous_apply v).comp ((continuous_apply g).comp hc)

theorem continuous_representationFromHom (Γ : Type*) [Group Γ] :
    @Continuous (OperatorCoding.UnitaryRepresentation Γ) (Representation Γ)
      (OperatorCoding.unitaryRepresentationTopology Γ) (representationStrongTopology Γ)
      representationFromHom := by
  letI : TopologicalSpace (Representation Γ) := representationStrongTopology Γ
  letI : TopologicalSpace (OperatorCoding.UnitaryRepresentation Γ) :=
    OperatorCoding.unitaryRepresentationTopology Γ
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro g
  apply continuous_pi
  intro v
  exact (OperatorCoding.strongUnitary_continuous_eval v).comp
    ((continuous_apply g).comp continuous_induced_dom)

theorem representationEquivalent_iff {Γ : Type*} [Group Γ] (ρ σ : Representation Γ) :
    RepresentationEquivalent ρ σ ↔
      OperatorCoding.UnitaryRepresentationEquivalent (representationToHom ρ) (representationToHom σ) := by
  constructor
  · rintro ⟨U,hU⟩
    refine ⟨U,fun g => ?_⟩
    apply LinearIsometryEquiv.ext
    intro v
    change U (ρ.operator g (U.symm v)) = σ.operator g v
    rw [hU]
    simp
  · rintro ⟨U,hU⟩
    refine ⟨U,fun g v => ?_⟩
    have h := congrArg (fun W : OperatorCoding.StrongUnitary OperatorCoding.CanonicalHilbert => W (U v)) (hU g)
    simpa using h

theorem representations_borelBireducible (Γ : Type*) [Group Γ] :
    BorelBireducibleWith (representationBorel Γ) (OperatorCoding.unitaryRepresentationBorel Γ)
      RepresentationEquivalent OperatorCoding.UnitaryRepresentationEquivalent := by
  constructor
  · refine ⟨representationToHom, ?_, representationEquivalent_iff⟩
    exact @Continuous.borel_measurable _ _ (representationStrongTopology Γ)
      (OperatorCoding.unitaryRepresentationTopology Γ) _ (continuous_representationToHom Γ)
  · refine ⟨representationFromHom, ?_, ?_⟩
    · exact @Continuous.borel_measurable _ _ (OperatorCoding.unitaryRepresentationTopology Γ)
        (representationStrongTopology Γ) _ (continuous_representationFromHom Γ)
    · intro ρ σ
      simpa only [(representationEquiv Γ).apply_symm_apply] using
        (representationEquivalent_iff (representationFromHom ρ) (representationFromHom σ)).symm













end BenchmarkComparisons

end
end Source21

open BenchmarkComparisons in
theorem solution :
    BorelBireducibleWith (representationBorel (FreeGroup ℕ)) operatorBorel
      RepresentationEquivalent OperatorEquivalent := by
  constructor
  · exact OperatorCoding.borelReducesWith_trans
      (representations_borelBireducible (FreeGroup ℕ)).1
      OperatorCoding.freeRepresentations_borelReduce_boundedOperators
  · exact OperatorCoding.borelReducesWith_trans
      OperatorCoding.boundedOperators_borelReduce_freeRepresentations
      (representations_borelBireducible (FreeGroup ℕ)).2

#print axioms solution
