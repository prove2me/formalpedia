-- Prove2me | Theorems.Thm_riemann_hypothesis_imp_zeta_ne_zero_of_half_lt_re
-- name    : riemann_hypothesis_imp_zeta_ne_zero_of_half_lt_re
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T11:06:25.02093+00:00
-- url     : https://prove2.me/theorems/8103bc90-d46c-4d6a-959b-36ee4c5963f1
-- title:
--   The Riemann hypothesis implies $\zeta(s)\neq0$ for $\operatorname{Re} s>1/2$
-- statement:
--   Let $\zeta$ be the Riemann zeta function and let RH denote the Riemann hypothesis in the form 'every zero of $\zeta$ other than the trivial zeros $-2,-4,-6,\dots$ and the point $s=1$ has real part $\tfrac12$'. This theorem is the implication
--
--   $$\mathrm{RH}\;\Longrightarrow\;\bigl(\operatorname{Re} s>\tfrac12\Rightarrow\zeta(s)\neq0\bigr).$$
--
--   It is the routine direction of the equivalence between the Riemann hypothesis and its zero-free half-plane form: a zero with $\operatorname{Re} s>\tfrac12$ is neither a trivial zero (those have negative real part) nor the point $s=1$ (where $\zeta$ does not vanish), so RH would force its real part to equal $\tfrac12$.
--
--   Its role is bookkeeping of a decomposition: together with the converse reduction of RH to the half-plane statement, it certifies that the zero-free half-plane target is exactly equivalent to RH and not a strictly stronger assertion.
--
--   **Formalization Note.** `RiemannHypothesis` is Mathlib's predicate on `riemannZeta`, taken as a hypothesis here; the theorem is a conditional statement and asserts nothing unconditionally about the zeros of $\zeta$.
-- source:
--   Equivalence of the Riemann hypothesis with the absence of zeros in the half-plane Re(s) > 1/2: https://en.wikipedia.org/wiki/Riemann_hypothesis . The predicate `RiemannHypothesis` is Mathlib's, as used by the mission goal theorem `riemann_hypothesis`.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex

theorem riemann_hypothesis_imp_zeta_ne_zero_of_half_lt_re (h : RiemannHypothesis) (s : ℂ)
    (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by sorry
