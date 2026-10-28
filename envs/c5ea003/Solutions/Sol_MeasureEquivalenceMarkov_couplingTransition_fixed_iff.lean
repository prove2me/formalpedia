-- Prove2me | solution 1 for MeasureEquivalenceMarkov.couplingTransition_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:22:17.042865+00:00
-- url     : https://prove2.me/submissions/026c9a9d-69dd-4e2f-99d0-247dceff657f

import Definitions.Def_BenchmarkOperator20261026_CouplingMarkov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

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

-- Preserved source skeleton: CouplingMarkov
section
/-!
A stationary coupling gives an actual contraction of L2. The operator
is the adjoint of the first-coordinate pullback followed by the
second-coordinate pullback. Its fixed vectors are precisely the
functions with equal pullbacks on the coupling.
-/

open MeasureTheory Filter
open scoped InnerProduct

namespace MeasureEquivalenceMarkov

section Hilbert

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]





theorem isometryTransition_fixed_iff (i j : E →ₗᵢ[ℝ] F) (x : E) :
    isometryTransition i j x = x ↔ i x = j x := by
  constructor
  · intro hx
    have hip : inner ℝ (i x) (j x) = ‖x‖ ^ 2 := by
      change inner ℝ (i.toContinuousLinearMap x) (j.toContinuousLinearMap x) = ‖x‖ ^ 2
      rw [← ContinuousLinearMap.adjoint_inner_right]
      change inner ℝ x (isometryTransition i j x) = ‖x‖ ^ 2
      rw [hx, real_inner_self_eq_norm_sq]
    have hnorm : ‖i x - j x‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, i.norm_map, j.norm_map, hip]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
  · intro hx
    change i.toContinuousLinearMap.adjoint (j x) = x
    rw [← hx]
    exact congrArg (fun A : E →L[ℝ] E => A x) i.adjoint_comp_self

end Hilbert

section Coupling

variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)











end Coupling

end MeasureEquivalenceMarkov

end

/-!
A stationary coupling gives an actual contraction of L2. The operator
is the adjoint of the first-coordinate pullback followed by the
second-coordinate pullback. Its fixed vectors are precisely the
functions with equal pullbacks on the coupling.
-/
open MeasureTheory Filter
open scoped InnerProduct
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
open MeasureEquivalenceMarkov
variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

theorem solution (f : Lp ℝ 2 μ) :
    couplingTransition μ J hfst hsnd f = f ↔
      ∀ᵐ z ∂J, f z.1 = f z.2 := by
  rw [couplingTransition, isometryTransition_fixed_iff]
  constructor
  · intro h
    have hae : couplingFirst μ J hfst f =ᵐ[J] couplingSecond μ J hsnd f :=
      Eventually.of_forall (fun z => congrArg (fun u : Lp ℝ 2 J => u z) h)
    filter_upwards [hae,
      Lp.coeFn_compMeasurePreserving f (show MeasurePreserving Prod.fst J μ from ⟨measurable_fst, hfst⟩),
      Lp.coeFn_compMeasurePreserving f (show MeasurePreserving Prod.snd J μ from ⟨measurable_snd, hsnd⟩)]
      with z hz h1 h2
    exact h1.symm.trans (hz.trans h2)
  · intro h
    apply Lp.ext
    filter_upwards [h,
      Lp.coeFn_compMeasurePreserving f (show MeasurePreserving Prod.fst J μ from ⟨measurable_fst, hfst⟩),
      Lp.coeFn_compMeasurePreserving f (show MeasurePreserving Prod.snd J μ from ⟨measurable_snd, hsnd⟩)]
      with z hz h1 h2
    exact h1.trans (hz.trans h2.symm)
