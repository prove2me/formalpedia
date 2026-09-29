-- Prove2me | Theorems.Thm_mme_stothers_theorem53_global_value
-- name    : mme_stothers_theorem53_global_value
-- status  : Disproved
-- author  : @marwahaha
-- created : 2026-08-29T00:20:44.633121+00:00
-- url     : https://prove2.me/theorems/03f3b48b-f8b2-4507-b50d-20a14e33c1f0
-- title:
--   Theorem 5.3: kernel-corrected fourth-power value inequality
-- statement:
--   Let $K$ be an arbitrary field, let $2\le3\tau\le3$, and let $a,b\in\mathbb R^{10}$ have strictly positive coordinates. Assume $a\in Z$, $b\in\mathcal N$, and $a-b$ lies in the displayed two-dimensional kernel of $Q$. Write $A=Qa/3$, let $n_i$ be the Table 1 multiplicities, and let $v_i$ be its ten cubed constituent-value bounds at $q=6$ and $\rho=3\tau$.
--
--   Let
--
--   $$
--   R=\prod_{i=1}^{10}
--   \left(v_i^{a_i/3}a_i^{a_i}b_i^{-b_i}\right)^{n_i}
--   \prod_{j=0}^{8}A_j^{-A_j}.
--   $$
--
--   For every fixed real $V$ which is nonnegative and strictly smaller than $R$, the literal fourth power $CW_6^{\otimes4}$ has tau-value at least $V$.
--
--   This is the interior, field-uniform and source-faithful exponential-rate form of Davie--Stothers Theorem 5.3 and Equation (5.3). The strict lower base accounts for subexponential losses in the finite extraction while retaining the full limiting rate needed for the numerical endpoint.
-- source:
--   Davie and Stothers (2013), Theorem 5.3 and Equation (5.3), printed p. 368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_theorem53_global_value
    {K : Type u} [Field K]
    (tau : Real) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (a b : Fin 10 → Real)
    (ha : MME.StothersFourth.InZ a)
    (hb : MME.StothersFourth.InN b)
    (haPos : ∀ i : Fin 10, 0 < a i)
    (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i => a i - b i)) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau a b →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6) tau V := by
  sorry
