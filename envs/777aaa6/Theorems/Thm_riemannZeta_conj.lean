-- Prove2me | Theorems.Thm_riemannZeta_conj
-- name    : riemannZeta_conj
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T12:28:38.097294+00:00
-- url     : https://prove2.me/theorems/26a08613-12ba-4999-89b5-820376f54e39
-- title:
--   Schwarz reflection for $\zeta$: $\zeta(\bar s)=\overline{\zeta(s)}$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function, defined on all of $\mathbb{C}$ by analytic continuation. The assertion is the reflection identity
--
--   $$\zeta(\bar s)=\overline{\zeta(s)}\qquad\text{for every }s\in\mathbb{C}.$$
--
--   Equivalently, $\zeta$ is real on the real axis and therefore satisfies the Schwarz reflection principle. An immediate consequence is that the zeros of $\zeta$ are symmetric about the real axis: $\zeta(s)=0$ if and only if $\zeta(\bar s)=0$. Together with the functional equation, which gives symmetry under $s\mapsto 1-s$, this is one of the two symmetries of the zero set of $\zeta$, and it lets one restrict attention to zeros in the upper half-plane.
--
--   The identity holds for all $s$, including the exceptional points $s=0$ and $s=1$ where Mathlib's `riemannZeta` takes specific finite values (at $s=1$ the value is real, and $\zeta(0)=-1/2$).
--
--   **Formalization note.** `starRingEnd ℂ` is complex conjugation.
-- source:
--   Classical; the reflection principle for the Riemann zeta function. See e.g. Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., §2.1.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem riemannZeta_conj (s : ℂ) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by sorry
