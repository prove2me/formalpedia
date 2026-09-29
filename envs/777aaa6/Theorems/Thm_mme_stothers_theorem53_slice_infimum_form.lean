-- Prove2me | Theorems.Thm_mme_stothers_theorem53_slice_infimum_form
-- name    : mme_stothers_theorem53_slice_infimum_form
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T18:20:41.816653+00:00
-- url     : https://prove2.me/theorems/fa462666-8f6e-4e28-b648-78e378ed7b58
-- title:
--   Theorem 5.3 from the attained same-marginal minimum
-- statement:
--   Davie--Stothers Theorem 5.3 with the same-marginal minimum supplied as a hypothesis rather than through the algebraic description of where it sits.
--
--   Let $K$ be a field, $\tfrac23\le\tau\le1$, and let $a,b\in Z$ be strictly positive with $a-b\in Y$. Suppose $b$ minimises the Lemma 5.2 weight over the whole affine slice:
--   $$\prod_i b_i^{\,n_ib_i}\;\le\;\prod_i c_i^{\,n_ic_i}\qquad\text{for every }c\in Z\text{ with }c-b\in Y .$$
--   Then for every $V$ with
--   $$0\;\le\;V\;<\;\Bigl(\prod_{i}v_i^{\,n_ia_i/3}\Bigr)\Bigl(\prod_{j}A_j^{-A_j}\Bigr)\cdot\frac{\prod_i b_i^{\,n_ib_i}}{\prod_i a_i^{\,n_ia_i}},\qquad A=\tfrac13Qa,$$
--   the literal fourth power $\mathrm{CW}_6^{\otimes4}$ has $\tau$-value at least $V$.
--
--   **Role.** This is the extraction half of Theorem 5.3, separated from its arithmetic half. Equation (3.4) of the source bounds the star count of the hashing step by $\prod_jA_j^{-A_j}$ times $\inf_{D\in\Lambda_E}\prod_\mu D_\mu^{D_\mu}\big/\prod_\mu E_\mu^{E_\mu}$, an infimum over the profiles sharing the marginals of the profile $E=a$ that is actually used. What the extraction consumes is only that the displayed $b$ *attains* that infimum — the extremal property stated above. Lemma 5.2 is what identifies the attaining point: it shows that the stationary set $\mathcal N$, cut out by $b_3b_8^2=b_5b_6b_{10}$ and $b_4b_8b_9=b_5b_7b_{10}$, consists exactly of the slice minimisers, because those two equations say precisely that the gradient of $\sum_in_ib_i\log b_i$ vanishes along the two kernel directions $\sigma$ and $\tau$.
--
--   Splitting the theorem this way keeps the algebraic characterisation of $\mathcal N$ — already proved — out of the combinatorial argument, which needs only the inequality.
-- source:
--   A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proceedings of the Royal Society of Edinburgh 143A (2013) 351-369; Equation (3.4) on printed p. 358 and Lemma 5.2 / Theorem 5.3 on printed p. 368. https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_theorem53_slice_infimum_form
    {K : Type u} [Field K]
    (tau : Real) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (a b : Fin 10 → Real)
    (ha : MME.StothersFourth.InZ a)
    (hbZ : MME.StothersFourth.InZ b)
    (haPos : ∀ i : Fin 10, 0 < a i)
    (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i => a i - b i))
    (hmin : ∀ c : Fin 10 → Real, MME.StothersFourth.InZ c →
      MME.StothersFourth.InY (fun i => c i - b i) →
      MME.StothersFourth.entropyProduct b ≤ MME.StothersFourth.entropyProduct c) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau a a *
            (MME.StothersFourth.entropyProduct b /
              MME.StothersFourth.entropyProduct a) →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6) tau V := by
  sorry
