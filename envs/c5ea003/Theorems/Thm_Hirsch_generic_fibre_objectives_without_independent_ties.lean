-- Prove2me | Theorems.Thm_Hirsch_generic_fibre_objectives_without_independent_ties
-- name    : Hirsch.generic_fibre_objectives_without_independent_ties
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T02:15:22.032236+00:00
-- url     : https://prove2.me/theorems/d323320e-6843-4743-a2ea-e46b770cb3c8
-- title:
--   Generic objective segments preserve finite endpoint cones and avoid independent simultaneous ties
-- statement:
--   Let E be a real vector space, let C0 and C1 be finite lists of strict comparison vectors, and let V be a finite list of nonzero difference vectors. Suppose linear objectives f0 and g0 are strictly negative on C0 and C1 respectively. There exist linear objectives f,g retaining those respective strict comparisons, nonzero on every listed difference, and satisfying
--
--   $$f(v_i)g(v_j)-f(v_j)g(v_i)\ne0$$
--
--   whenever v_i,v_j are linearly independent. Consequently the entire affine objective line has no independent simultaneous ties:
--
--   $$((1-t)f+tg)(v_i)=((1-t)f+tg)(v_j)=0\quad\Longrightarrow\quad v_j\in\operatorname{span}\{v_i\}.$$
--
--   This holds for every real t. For finite Minkowski factors, use the nonzero within-factor point differences as V and the comparisons selecting the desired endpoint vertices in C0,C1. Common strict core comparisons are preserved throughout 0<=t<=1. The result supplies generic-objective existence, not a presumed normal-fan condition. It does not by itself enumerate crossings, assemble their supporting segments, certify Python output, find a decomposition, or prove a uniform graph-diameter bound. Empty comparison lists and empty V are permitted. No finite ambient dimension is assumed.
-- source:
--   Deza--Pournin, arXiv:1806.07643v1, section 3 Lemma 3.7 (classical generic fibre path). Explicit finite determinant construction: research/DETERMINISTIC_FIBRE_PATH.md sections 3-4 in this bundle. Uses pinned Mathlib/Algebra/Module/Submodule/Union.lean, Module.exists_dual_forall_apply_ne_zero. Complements accepted PR239 and distinct active PR240 in jjoshua2/prove2me-work. No historical novelty claim.

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.generic_fibre_objectives_without_independent_ties
    {E A B I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype A] [Fintype B] [Fintype I]
    (f₀ g₀ : E →ₗ[ℝ] ℝ) (c₀ : A → E) (c₁ : B → E) (v : I → E)
    (hc₀ : ∀ a, f₀ (c₀ a) < 0)
    (hc₁ : ∀ b, g₀ (c₁ b) < 0)
    (hv : ∀ i, v i ≠ 0) :
    ∃ f g : E →ₗ[ℝ] ℝ,
      (∀ a, f (c₀ a) < 0) ∧
      (∀ b, g (c₁ b) < 0) ∧
      (∀ i, f (v i) ≠ 0) ∧
      (∀ i, g (v i) ≠ 0) ∧
      (∀ i j, v j ∉ Submodule.span ℝ ({v i} : Set E) →
        f (v i)*g (v j)-f (v j)*g (v i) ≠ 0) ∧
      ∀ (t : ℝ) (i j : I),
        ((1-t)*f (v i)+t*g (v i)=0) →
        ((1-t)*f (v j)+t*g (v j)=0) →
        v j ∈ Submodule.span ℝ ({v i} : Set E) := by sorry
