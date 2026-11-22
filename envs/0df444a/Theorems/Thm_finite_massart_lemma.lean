-- Prove2me | Theorems.Thm_finite_massart_lemma
-- name    : finite_massart_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:25.031787+00:00
-- url     : https://prove2.me/theorems/96cddf0b-e727-4f1c-b7b3-883ab4c837cc
-- title:
--   finite massart lemma: finite massart lemma
-- statement:
--   Massart finite lemma: E_σ[max_{j ≤ N} Z_j] ≤ σ√(2 log N).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L419-L588
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L419-L588

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem finite_massart_lemma {m : ℕ} (_hm : 0 < m) {N : ℕ} (hN : 0 < N)
    (Z : Fin N → SignVector m → ℝ) (σ_param : ℝ) (hσ : 0 < σ_param)
    (h_mgf : ∀ j t, 0 ≤ t →
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
      Real.exp (t ^ 2 * σ_param ^ 2 / 2)) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ sv : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv) ≤
    σ_param * Real.sqrt (2 * Real.log N) := by sorry
