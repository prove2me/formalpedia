-- Prove2me | solution 1 for MeasureEquivalenceInducedCorners.exists_induced_corner_transport
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:31:16.165886+00:00
-- url     : https://prove2.me/submissions/fbb71104-6e17-46c6-8995-8d51e36d35e7

import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_MeasureEquivalenceEquidecomposition_exists_equidecomposition
import Theorems.Thm_MeasureEquivalenceEquidecomposition_exists_piecewise_measure_transport
import Theorems.Thm_MeasureEquivalenceEquidecomposition_restrict_eq_sum_of_disjoint_cover

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

-- Preserved source skeleton: InducedCornerTransport
section
/-! Genuine finite-corner induced-module transports on the product of
the base sample space and the counting-measure group coordinate. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceInducedCorners

noncomputable section

open MeasureEquivalenceEquidecomposition

variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]















theorem diagonal_orbitPoint (g : G) (p : Z × G) :
    orbitPoint (diagonalEquiv g p) = orbitPoint p := by
  change (p.2 * g⁻¹) • (g • p.1) = p.2 • p.1
  simp only [mul_smul, inv_smul_smul]

theorem diagonal_indexShift (g h : G) (p : Z × G) :
    diagonalEquiv g (indexShift h p) = indexShift h (diagonalEquiv g p) := by
  change (g • p.1, (h*p.2)*g⁻¹) = (g • p.1, h*(p.2*g⁻¹))
  rw [mul_assoc]



omit [Group G] [MeasurableSingletonClass G] [MulAction G Z] [MeasurableConstSMul G Z] in
theorem cornerMeasure_eq_restrict (μ : Measure Z) [SigmaFinite μ] (A : Set Z) :
    cornerMeasure (G := G) μ A = (μ.prod (Measure.count : Measure G)).restrict (A ×ˢ univ) := by
  simpa only [cornerMeasure, Measure.restrict_univ] using
    (Measure.prod_restrict (μ := μ) (ν := (Measure.count : Measure G)) A univ)

variable (μ : Measure Z) [SigmaFinite μ]
    (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)

include hmp in
theorem diagonal_preserving (g : G) :
    MeasurePreserving (diagonalEquiv (Z := Z) g)
      (μ.prod (Measure.count : Measure G)) (μ.prod Measure.count) :=
  (hmp g).prod (count_preserving (indexRight g⁻¹))





end
end MeasureEquivalenceInducedCorners

end

/-! Genuine finite-corner induced-module transports on the product of
the base sample space and the counting-measure group coordinate. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
open MeasureEquivalenceInducedCorners
open MeasureEquivalenceEquidecomposition
variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]
variable (μ : Measure Z) [SigmaFinite μ]
    (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)

include hmp

theorem solution
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (A B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    ∃ F H : (Z × G) → (Z × G),
      MeasurePreserving F (cornerMeasure μ A) (cornerMeasure μ B) ∧
      MeasurePreserving H (cornerMeasure μ B) (cornerMeasure μ A) ∧
      (∀ᵐ p ∂cornerMeasure μ A, H (F p) = p) ∧
      (∀ᵐ p ∂cornerMeasure μ B, F (H p) = p) ∧
      (∀ᵐ p ∂cornerMeasure μ A, orbitPoint (F p) = orbitPoint p) ∧
      (∀ h : G, ∀ᵐ p ∂cornerMeasure μ A,
        F (indexShift h p) = indexShift h (F p)) := by
  obtain ⟨e, C, T, hm, hsub, hCdis, hTdis, heq, hcoverA, hcoverB⟩ :=
    exists_equidecomposition μ hmp herg A B hA hB hfin hmass
  let ν := μ.prod (Measure.count : Measure G)
  let CS : ℕ → Set (Z × G) := fun n => C n ×ˢ univ
  let TS : ℕ → Set (Z × G) := fun n => T n ×ˢ univ
  have hCSm : ∀ n, MeasurableSet (CS n) := fun n => (hm n).1.prod MeasurableSet.univ
  have hTSm : ∀ n, MeasurableSet (TS n) := fun n => (hm n).2.prod MeasurableSet.univ
  have hCSdis : Pairwise (fun i j => Disjoint (CS i) (CS j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact Set.disjoint_left.mp (hCdis hij) hi.1 hj.1
  have hTSdis : Pairwise (fun i j => Disjoint (TS i) (TS j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact Set.disjoint_left.mp (hTdis hij) hi.1 hj.1
  have hCSA : ν ((A ×ˢ univ) \ ⋃ n, CS n) = 0 := by
    have hs : (A ×ˢ (univ : Set G)) \ ⋃ n, CS n = (A \ ⋃ n, C n) ×ˢ univ := by
      ext p
      simp only [CS, mem_diff, mem_prod, mem_univ, mem_iUnion, and_true]
    rw [hs, Measure.prod_prod, hcoverA, zero_mul]
  have hTSB : ν ((B ×ˢ univ) \ ⋃ n, TS n) = 0 := by
    have hs : (B ×ˢ (univ : Set G)) \ ⋃ n, TS n = (B \ ⋃ n, T n) ×ˢ univ := by
      ext p
      simp only [TS, mem_diff, mem_prod, mem_univ, mem_iUnion, and_true]
    rw [hs, Measure.prod_prod, hcoverB, zero_mul]
  have himage (n : ℕ) : diagonalEquiv (e n) '' CS n = TS n := by
    ext p
    constructor
    · rintro ⟨⟨x,d⟩, hx, rfl⟩
      refine ⟨?_, mem_univ _⟩
      rw [heq]
      change (e n)⁻¹ • (e n • x) ∈ C n
      simpa only [inv_smul_smul] using hx.1
    · rintro ⟨hp, _⟩
      rw [heq] at hp
      refine ⟨((e n)⁻¹ • p.1, p.2 * e n), ⟨hp, mem_univ _⟩, ?_⟩
      change (e n • ((e n)⁻¹ • p.1), (p.2 * e n) * (e n)⁻¹) = p
      simp only [smul_inv_smul, mul_inv_cancel_right, Prod.mk.eta]
  obtain ⟨F,H,hF,hH,hFC,hHT,hHF,hFH⟩ := exists_piecewise_measure_transport ν
    (A ×ˢ univ) (B ×ˢ univ) CS TS hCSm hTSm
    (fun n p hp => ⟨(hsub n).1 hp.1, mem_univ _⟩)
    (fun n p hp => ⟨(hsub n).2 hp.1, mem_univ _⟩)
    hCSdis hTSdis hCSA hTSB (fun n => diagonalEquiv (e n))
    (fun n => diagonal_preserving μ hmp (e n)) himage
  have hsumA := restrict_eq_sum_of_disjoint_cover ν (A ×ˢ univ) CS hCSm
    (fun n p hp => ⟨(hsub n).1 hp.1, mem_univ _⟩) hCSdis hCSA
  have hAeq := cornerMeasure_eq_restrict (G := G) (μ := μ) A
  have hBeq := cornerMeasure_eq_restrict (G := G) (μ := μ) B
  simp only [ν, ← hAeq, ← hBeq] at hF hH hHF hFH
  refine ⟨F,H,hF,hH,hHF,hFH,?_,?_⟩
  · rw [hAeq, hsumA, Measure.ae_sum_iff]
    intro n
    filter_upwards [ae_restrict_mem (hCSm n)] with p hp
    rw [hFC n hp]
    exact diagonal_orbitPoint (e n) p
  · intro h
    rw [hAeq, hsumA, Measure.ae_sum_iff]
    intro n
    filter_upwards [ae_restrict_mem (hCSm n)] with p hp
    have hshift : indexShift h p ∈ CS n := ⟨hp.1, mem_univ _⟩
    rw [hFC n hshift, hFC n hp]
    exact diagonal_indexShift (e n) h p
