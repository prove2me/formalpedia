-- Prove2me | Theorems.Thm_mme_stothers_theorem53_global_value_corrected
-- name    : mme_stothers_theorem53_global_value_corrected
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T15:36:52.551829+00:00
-- url     : https://prove2.me/theorems/5c9815ab-79c2-4c7b-b7d6-2db86328c48a
-- title:
--   Theorem 5.3 with the combination loss in the direction of Equation (3.4)
-- statement:
--   Davie--Stothers Theorem 5.3, with the same-marginal correction in the direction forced by Equation (3.4).
--
--   Let $K$ be a field, let $\tfrac23\le\tau\le1$, let $a\in Z$ and $b\in\mathcal N$ be strictly positive with $a-b\in Y$, and put $A=\tfrac13Qa$. Then for every $V$ with
--   $$0\;\le\;V\;<\;\Bigl(\prod_{i=1}^{10}v_i^{\,n_ia_i/3}\Bigr)\Bigl(\prod_{j=0}^{8}A_j^{-A_j}\Bigr)\cdot\frac{\prod_{i}b_i^{\,n_ib_i}}{\prod_{i}a_i^{\,n_ia_i}}$$
--   the literal fourth power $\mathrm{CW}_6^{\otimes4}$ has $\tau$-value at least $V$.
--
--   The first two factors are `globalRate 6 tau a a`, the rate of the profile $a$ with no correction; the third is `entropyProduct b / entropyProduct a`, which by Lemma 5.2 is at most $1$.
--
--   **Where the direction comes from.** Equation (3.4) of the source bounds the star count of the hashing step by
--   $$\prod_{k}A_k^{-A_k}\cdot\inf_{D\in\Lambda_E}\prod_\mu\frac{D_\mu^{D_\mu}}{E_\mu^{E_\mu}},$$
--   where $E$ is the profile used and $\Lambda_E$ is the set of profiles with the same marginals. Since $E\in\Lambda_E$, that infimum is at most $1$: it is the combination loss, the price of the hash being unable to separate profiles sharing a marginal. Lemma 5.2 identifies the infimum — it is attained at the stationary point $b\in\mathcal N$ of the slice — so with $E=a$ the factor is $\prod_ib_i^{n_ib_i}\big/\prod_ia_i^{n_ia_i}\le1$, which is what appears above.
--
--   **Formalization note.** The existing node `mme_stothers_theorem53_global_value` states the same conclusion with `globalRate 6 tau a b`, whose correction factor is the reciprocal $\prod_ia_i^{n_ia_i}\big/\prod_ib_i^{n_ib_i}\ge1$. The two agree when $a=b$, which is the case discharged by `mme_stothers_fixed_profile_fourth_value_below_globalRate`, so the proved $\omega<2.3737$ route is unaffected; they differ whenever $a\neq b$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proceedings of the Royal Society of Edinburgh 143A (2013) 351-369; Equation (3.4) on printed p. 358, Lemma 5.2 and Theorem 5.3 on printed p. 368. https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_theorem53_global_value_corrected
    {K : Type u} [Field K]
    (tau : Real) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (a b : Fin 10 → Real)
    (ha : MME.StothersFourth.InZ a)
    (hb : MME.StothersFourth.InN b)
    (haPos : ∀ i : Fin 10, 0 < a i)
    (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i => a i - b i)) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau a a *
            (MME.StothersFourth.entropyProduct b /
              MME.StothersFourth.entropyProduct a) →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6) tau V := by
  sorry
