-- Prove2me | Theorems.Thm_rademacher_mgf_bound
-- name    : rademacher_mgf_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:03.203049+00:00
-- url     : https://prove2.me/theorems/ef83ab11-a9a2-42d5-b12c-fa6e689dbced
-- title:
--   rademacher mgf bound: rademacher mgf bound
-- statement:
--   Rademacher MGF bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L331-L416
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L331-L416

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem rademacher_mgf_bound {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (c : ℝ) (_hc : 0 ≤ c)
    (ha : ∀ i, |a i| ≤ c) (t : ℝ) (_ht : 0 ≤ t) :
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ σ : SignVector m, Real.exp (t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) ≤
    Real.exp (t ^ 2 * c ^ 2 / (2 * m)) := by sorry
