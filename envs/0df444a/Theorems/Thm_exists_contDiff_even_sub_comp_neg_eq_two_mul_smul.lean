-- Prove2me | Theorems.Thm_exists_contDiff_even_sub_comp_neg_eq_two_mul_smul
-- name    : exists_contDiff_even_sub_comp_neg_eq_two_mul_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/5f6a134d-ef0c-5d79-bef2-0852f4540ba6
-- title:
--   Smooth even Hadamard factorisation of the odd part
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F$ a complete real normed space, and let $B : E \times \mathbb{R} \to F$ be $C^\infty$ (`ContDiff ℝ ⊤`). Then there exists a map $Q : E \times \mathbb{R} \to F$ which is again $C^\infty$, which is even in its last variable in the sense that $Q(e,-\rho) = Q(e,\rho)$ for all $e \in E$ and all $\rho \in \mathbb{R}$, and which satisfies $$B(e,\rho) - B(e,-\rho) = (2\rho)\cdot Q(e,\rho)$$ for all $e \in E$ and $\rho \in \mathbb{R}$, the scalar $2\rho$ acting on $F$ by its real scalar multiplication. Thus the odd part of $B$ in the last variable factors as $\rho$ times a globally smooth function that is even in $\rho$; no compact support or decay assumption is imposed on $B$, and the statement is an existence assertion, with no uniqueness or explicit formula for $Q$ claimed.
--
--   This is Hadamard's division lemma with parameters, in the form adapted to reflection in the last variable: the odd part of a smooth function vanishes to first order on $\rho = 0$ and the quotient may be chosen smooth and even. It is used in the even-reflection step that splits a smooth function of $|\rho|$ into a smooth even part plus $|\rho|$ times a smooth factor, and is cited by [`MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport`](thm.html#MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_contDiff_even_sub_comp_neg_eq_two_mul_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_contDiff_even_sub_comp_neg_eq_two_mul_smul
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (B : E × ℝ → F) (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    ∃ Q : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) Q ∧ (∀ (e : E) (ρ : ℝ), Q (e, -ρ) = Q (e, ρ)) ∧
      ∀ (e : E) (ρ : ℝ), B (e, ρ) - B (e, -ρ) = (2 * ρ) • Q (e, ρ) := by sorry
