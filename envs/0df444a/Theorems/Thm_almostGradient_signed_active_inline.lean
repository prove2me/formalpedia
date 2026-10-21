-- Prove2me | Theorems.Thm_almostGradient_signed_active_inline
-- name    : almostGradient_signed_active_inline
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T14:12:26.126012+00:00
-- url     : https://prove2.me/theorems/5700a479-2bcc-4e8a-9110-93e8cb4dfa5c
-- title:
--   almostGradient_signed_active_inline
-- statement:
--   Automatically extracted helper theorem almostGradient_signed_active_inline from oversized parent candidate 7f4c354e64e85fbbc0c4e0c7c9f542873a32821b88d4dd319805274de277d4f9.
-- source:
--   candidate-decomposition:e816baae-7e8d-45ed-a260-8035c5cda886:7f4c354e64e85fbbc0c4e0c7c9f542873a32821b88d4dd319805274de277d4f9

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_local_inverse_bound
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_active_signed_inner_approx
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_differentiable_gradient_signed_active
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq

theorem almostGradient_signed_active_inline {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, maxResidual ψ x ≠ 0 →
      ∀ g ∈ ShorNonsmooth.AlmostDiff.almostGradients (maxResidual ψ) x,
        ∃ i : Fin n, ∃ σ : ℝ, σ ^ 2 = 1 ∧ g = σ • gradient (ψ i) x ∧
          σ * ψ i x = maxResidual ψ x ∧ |ψ i x| = maxResidual ψ x := by sorry
