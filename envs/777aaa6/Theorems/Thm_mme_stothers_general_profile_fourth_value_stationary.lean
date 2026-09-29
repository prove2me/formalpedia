-- Prove2me | Theorems.Thm_mme_stothers_general_profile_fourth_value_stationary
-- name    : mme_stothers_general_profile_fourth_value_stationary
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T05:47:33.420462+00:00
-- url     : https://prove2.me/theorems/1794031a-20dd-4657-99f2-b3a244db24c8
-- title:
--   Corrected Theorem 5.3 for an integral profile and a stationary partner
-- statement:
--   **The fourth-power value of a general integral profile, corrected by the combination loss.**
--
--   Work over a field $K$ at the Coppersmith--Winograd parameter $q=6$ and fix an exponent $\tau$.  Let $\beta$ and $\beta^{*}$ be strictly positive integral ten-class profiles with the same nine-grade marginals, $Q\beta^{*} = Q\beta$, and suppose the normalised partner $b = \beta^{*}/D$ is stationary, $b \in \mathcal N$.  Write $a = \beta/D$.  Assume the ten class constituents have their Lemma 5.1 values, i.e. the cyclically symmetrized constituent of class $r$ has tau-value at least $V$ for every $0 \le V < v_r(\tau)$, and that the fourth-power grading is supported in total degree eight.
--
--   Then for every
--
--   $$0 \le V \;<\; G(\tau,a)\,\frac{E(b)}{E(a)},
--   \qquad E(x) = \prod_{r} x_r^{\,c_r x_r},$$
--
--   the literal fourth power $CW_6^{\otimes 4}$ has tau-value at least $V$, where $G(\tau,a)$ is the Equation (5.3) global rate of $a$ against itself.
--
--   This is Theorem 5.3 of Davie--Stothers in the form the source actually supports.  The published statement of the platform's `mme_stothers_theorem53_global_value` carries the reciprocal factor $E(a)/E(b) \ge 1$ and is false; the correct factor is $E(b)/E(a) \le 1$, and it is the *combination loss* recorded as an infimum over the marginal fibre in Equation (3.4).  Its mechanism is visible here: the exact-profile targets of $\beta$ number $V_N \Delta_\beta$, but the completion star whose degree Behrend's construction must beat is governed by the maximum-entropy profile on the same marginal fibre, so the surviving family retains only the fraction $\Delta_\beta/\Delta_{\beta^{*}} = (E(b)/E(a))^N$ of them.
--
--   On the diagonal $\beta = \beta^{*}$ the correction is $1$ and the statement reduces to the published fixed-profile value; that is why the fixed chain, which lives only on the diagonal, never had to carry it, and why the $\omega < 2.3737$ endpoint it supports is unaffected.  What the general form adds is the freedom to vary $\beta$, which is exactly what an optimisation over profiles needs.
--
--   *Formalization note.* Stationarity of $b$ is used only through the Gibbs argument that makes $\beta^{*}$ entropy-maximal on its marginal fibre; no symmetrisation of the histogram is required.  The polynomial slack in the star-degree comparison is absorbed by choosing a strict intermediate endpoint, so no additional error constant appears in the conclusion.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Theorem 5.3 together with Section 3, Equations (3.2)-(3.4); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_general_profile_fourth_value_stationary
    {K : Type u} [Field K]
    (base bstar : Fin 10 → ℕ) (tau : ℝ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar))
    (hblockSupport : ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 →
        (∑ s, ((sigma s).val : ℕ)) = 8)
    (hclass : ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V → V < MME.StothersFourth.classValue 6 tau r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep r 0)
            (MME.StothersFourth.classRep r 1)
            (MME.StothersFourth.classRep r 2))) tau V) :
    ∀ V : ℝ, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau
            (MME.StothersFourth.genProfileB base)
            (MME.StothersFourth.genProfileB base) *
          (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
            MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base)) →
      HasTauValueAtLeast (MME.StothersFourth.cwFourthObj K 6) tau V := by
  sorry
