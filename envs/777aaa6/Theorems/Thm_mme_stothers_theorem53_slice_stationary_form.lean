-- Prove2me | Theorems.Thm_mme_stothers_theorem53_slice_stationary_form
-- name    : mme_stothers_theorem53_slice_stationary_form
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:57:10.883206+00:00
-- url     : https://prove2.me/theorems/8deb98d3-82ae-4d57-b1a5-e208a9ab4fbf
-- title:
--   Theorem 5.3 at a fixed pair, stationary form
-- statement:
--   **Davie--Stothers Theorem 5.3 at a fixed pair, in stationary form.**
--
--   Let $\tau$ satisfy $2\le 3\tau\le 3$, let $a\in Z$ be a strictly positive admissible profile, and
--   let $b\in\mathcal N$ be a strictly positive stationary profile on the same marginal fibre, i.e.
--   $a-b\in Y$. Then for every $V\ge 0$ with
--
--   $$V \;<\; \mathrm{globalRate}(6,\tau,a,a)\cdot\frac{\mathcal E(b)}{\mathcal E(a)},$$
--
--   the fourth power $CW_6^{\otimes 4}$ has $\tau$-value at least $V$.
--
--   This is the same statement as the slice-infimum form, with the minimality hypothesis on $b$
--   replaced by membership in $\mathcal N$. The two are interchangeable for the purposes of Theorem
--   5.3 -- Lemma 5.2 derives minimality from stationarity -- but stationarity is the more useful
--   hypothesis to carry into the extraction: it is exactly what makes $\log b$ an affine function of the
--   nine grade statistics, hence what identifies $b$'s histogram as the maximum-entropy one on the
--   fibre and so what controls the completion-star degree. The factor
--   $\mathcal E(b)/\mathcal E(a)\le1$ is the combination loss of Equation (3.4), and it degenerates to
--   $1$ exactly on the diagonal $a=b$, which is the case the published numerical endpoint uses.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Equations (3.2)-(3.4), and Section 5, Theorem 5.3 and Equation (5.3); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_theorem53_slice_stationary_form
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
