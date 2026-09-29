-- Prove2me | Theorems.Thm_mme_stothers_globalRate_correction_factor_ge_one
-- name    : mme_stothers_globalRate_correction_factor_ge_one
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T15:36:51.980828+00:00
-- url     : https://prove2.me/theorems/20b774c1-b0d0-4dd9-8776-4a8c030f9b16
-- title:
--   The globalRate same-marginal factor is at least one
-- statement:
--   The same-marginal correction factor carried by `globalRate` is at least one.
--
--   Let $a\in Z$ and $b\in\mathcal N$ be strictly positive with $a-b\in Y$, and write
--   $$\mathcal E(x)\;=\;\prod_{i=1}^{10}x_i^{\,n_ix_i}$$
--   for the weighted product of Lemma 5.2 (`entropyProduct`). Then
--
--   $$\mathrm{globalRate}(q,\tau,a,b)\;=\;\mathrm{globalRate}(q,\tau,a,a)\cdot\frac{\mathcal E(a)}{\mathcal E(b)},
--   \qquad \frac{\mathcal E(a)}{\mathcal E(b)}\;\ge\;1,$$
--
--   and consequently $\mathrm{globalRate}(q,\tau,a,a)\le\mathrm{globalRate}(q,\tau,a,b)$.
--
--   The factorisation is an identity: the two slots of `globalRate` differ only in the factor $\prod_i\bigl(a_i^{a_i}b_i^{-b_i}\bigr)^{n_i}=\mathcal E(a)/\mathcal E(b)$, and at $b=a$ that factor is $1$. The inequality is exactly Davie--Stothers Lemma 5.2, which says that the stationary point $b\in\mathcal N$ *minimises* $\mathcal E$ over the affine slice $(b+Y)\cap Z$.
--
--   **Why this is worth recording.** In the laser method the same-marginal set is a source of *loss*, not of gain: Equation (3.4) of the source bounds the surviving star count by
--   $$\prod_k A_k^{-A_k}\cdot\inf_{D\in\Lambda_E}\prod_\mu \frac{D_\mu^{D_\mu}}{E_\mu^{E_\mu}},$$
--   an infimum over a set that contains $E$ itself, hence a factor $\le 1$ — the combination loss. With $E=a$ the profile actually used and the infimum attained at $D=b$, that factor is $\mathcal E(b)/\mathcal E(a)$. The statement above shows that the factor built into `globalRate` is its reciprocal, and is therefore $\ge 1$ rather than $\le 1$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proceedings of the Royal Society of Edinburgh 143A (2013) 351-369; Equation (3.4) on printed p. 358, Lemma 5.2 and Theorem 5.3 on printed p. 368. https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_globalRate_correction_factor_ge_one
    (q : ℕ) (tau : ℝ) (a b : Fin 10 → ℝ)
    (ha : MME.StothersFourth.InZ a) (hb : MME.StothersFourth.InN b)
    (haPos : ∀ i : Fin 10, 0 < a i) (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i => a i - b i)) :
    MME.StothersFourth.globalRate q tau a b =
        MME.StothersFourth.globalRate q tau a a *
          (MME.StothersFourth.entropyProduct a /
            MME.StothersFourth.entropyProduct b) ∧
      1 ≤ MME.StothersFourth.entropyProduct a /
            MME.StothersFourth.entropyProduct b ∧
      MME.StothersFourth.globalRate q tau a a ≤
        MME.StothersFourth.globalRate q tau a b := by
  sorry
