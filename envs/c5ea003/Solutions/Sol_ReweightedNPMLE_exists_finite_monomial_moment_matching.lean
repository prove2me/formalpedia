-- Prove2me | solution 1 for ReweightedNPMLE.exists_finite_monomial_moment_matching
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:17.711845+00:00
-- url     : https://prove2.me/submissions/cfdd0a5a-9ae2-483b-87f7-81bcc9cf8f9a

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Theorems.Thm_ReweightedNPMLE_continuous_monomialFeature

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype
open ReweightedNPMLE in
/-- Compact-support moment matching: every probability-law moment vector has
an exactly matching discrete law with at most `choose(D+d,d)+1` slots.  Zero
masses pad representations using fewer atoms. -/
theorem solution
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ) (K : Set (Fin d → ℝ))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1) → Fin d → ℝ),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
        ∑ i, w i • monomialFeature d D (θ' i) =
          ∫ a, monomialFeature d D (θ a) ∂μ := by
  let C := convexHull ℝ (monomialFeature d D '' K)
  have hCcompact : IsCompact C := isCompact_convexHull_of_isCompact
    (hKcompact.image (continuous_monomialFeature d D))
  have hmean : (∫ a, monomialFeature d D (θ a) ∂μ) ∈ C := by
    apply (convex_convexHull ℝ _).integral_mem hCcompact.isClosed
    · filter_upwards [hθK] with a ha
      exact subset_convexHull ℝ _ ⟨θ a, ha, rfl⟩
    · exact hint
  have himage : (monomialFeature d D '' K).Nonempty := hKnonempty.image _
  obtain ⟨w, z, hw, hz, hsum⟩ :=
    exists_fixed_barycentric_representation himage hmean
  have hchoice : ∀ i, ∃ θ, θ ∈ K ∧ monomialFeature d D θ = z i := by
    intro i
    rcases hz i with ⟨θ, hθ, hθz⟩
    exact ⟨θ, hθ, hθz⟩
  choose θ' hθ'K hθ'z using hchoice
  refine ⟨w, θ', hw, hθ'K, ?_⟩
  simpa only [hθ'z] using hsum
