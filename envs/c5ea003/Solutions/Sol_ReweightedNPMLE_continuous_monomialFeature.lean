-- Prove2me | solution 1 for ReweightedNPMLE.continuous_monomialFeature
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:02:27.952845+00:00
-- url     : https://prove2.me/submissions/fd95f403-8070-4997-8170-e28114a8afa0

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

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype
open ReweightedNPMLE in
theorem solution (d D : ℕ) :
    Continuous (monomialFeature d D) := by
  apply continuous_pi
  intro m
  unfold monomialFeature monomialEval homogenizedVariable
  have hvar : ∀ i : Fin (d + 1), Continuous
      (fun a : Fin d → ℝ ↦ Fin.cases (motive := fun _ ↦ ℝ) 1 a i) := by
    intro i
    refine Fin.cases continuous_const (fun j ↦ continuous_apply j) i
  have hprod : ∀ s : Multiset (Fin (d + 1)),
      Continuous (fun a : Fin d → ℝ ↦
        (s.map (fun i ↦ Fin.cases (motive := fun _ ↦ ℝ) 1 a i)).prod) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simpa using (continuous_const : Continuous (fun _ : Fin d → ℝ ↦ (1 : ℝ)))
    | cons i s ih => simpa using (hvar i).mul ih
  exact hprod m.val
