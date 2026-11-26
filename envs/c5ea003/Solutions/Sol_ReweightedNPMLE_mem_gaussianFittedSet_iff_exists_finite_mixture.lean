-- Prove2me | solution 1 for ReweightedNPMLE.mem_gaussianFittedSet_iff_exists_finite_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:13:33.062902+00:00
-- url     : https://prove2.me/submissions/d6b7083b-e62e-4d63-8b5a-e6e5c69973cb

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FittedGeometry
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Compact fitted-value geometry

The infinite-dimensional mixing-law optimization is reduced to the compact
convex hull of the continuous Gaussian evaluation dictionary.  The compact
convex-hull theorem shows this is the actual finite-mixture hull, not merely
its closure, and the Gaussian lower bound keeps it in the positive orthant.
-/

open Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Membership in the fitted-value set is exactly representation by a finite
probability mixture of Gaussian dictionary atoms. -/
theorem solution
    {d n : ℕ} (x : Fin n → Point d) (K : Set (Point d))
    (v : Fin n → ℝ) :
    v ∈ gaussianFittedSet x K ↔
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (θ : ι → Point d),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, θ i ∈ K) ∧
          ∑ i, w i • gaussianScoreFeature x (θ i) = v := by
  constructor
  · intro hv
    obtain ⟨ι, hι, w, z, hw, hwsum, hz, hsum⟩ :=
      mem_convexHull_iff_exists_fintype.mp hv
    letI : Fintype ι := hι
    have hchoice : ∀ i, ∃ θ, θ ∈ K ∧ gaussianScoreFeature x θ = z i := by
      intro i
      rcases hz i with ⟨θ, hθ, hθz⟩
      exact ⟨θ, hθ, hθz⟩
    choose θ hθK hθz using hchoice
    refine ⟨ι, hι, w, θ, hw, hwsum, hθK, ?_⟩
    simpa only [hθz] using hsum
  · rintro ⟨ι, hι, w, θ, hw, hwsum, hθK, hsum⟩
    letI : Fintype ι := hι
    exact mem_convexHull_of_exists_fintype w
      (fun i ↦ gaussianScoreFeature x (θ i)) hw hwsum
      (fun i ↦ ⟨θ i, hθK i, rfl⟩) hsum
