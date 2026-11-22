-- Prove2me | Theorems.Thm_finite_support_vc_approx
-- name    : finite_support_vc_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:03.742247+00:00
-- url     : https://prove2.me/theorems/cdd910ff-41f2-483c-860d-79f47a34dcbb
-- title:
--   finite support vc approx: finite support vc approx
-- statement:
--   Finite-support distributions uniformly approximate any distribution on a VC class.
--   For a class of VC dimension at most `d` and any `ε > 0`, there exists
--   `T = T(d, ε)` such that every finitely supported distribution `μ` is within `ε`
--   (uniformly over the class) of some empirical distribution on `T` points. A
--   density-style reduction that lets the approximate minimax / MWU machinery, which lives
--   in finite support, apply to general distributions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/FiniteSupportUC.lean#L232-L431
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/FiniteSupportUC.lean#L232-L431

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
set_option autoImplicit true
@[expose] public section
public section
open Finset MeasureTheory
noncomputable section
universe u

theorem finite_support_vc_approx
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : ℕ) (hT : 0 < T),
      ∀ {H : Type*} [Fintype H] [DecidableEq H]
        (A : Finset (H → Bool)),
        A.boolVCDim ≤ d →
        ∀ μ : FinitePMF H, ∃ hs : Fin T → H,
          ∀ a ∈ A,
            |boolTestExpectation μ a -
              boolTestExpectation (empiricalPMF hT hs) a| ≤ ε := by sorry
