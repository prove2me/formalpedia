-- Prove2me | Theorems.Thm_zeta_nontrivial_zero_mem_critical_strip
-- name    : zeta_nontrivial_zero_mem_critical_strip
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T10:57:08.221312+00:00
-- url     : https://prove2.me/theorems/1f29c965-9767-4c65-a5a4-e90625aa6f48
-- title:
--   Nontrivial zeros of $\zeta$ lie in the critical strip $0<\operatorname{Re} s<1$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function, obtained by analytic continuation of $\sum_{n\ge 1} n^{-s}$ from the half-plane $\operatorname{Re} s>1$. Its *trivial zeros* are the points $s=-2,-4,-6,\dots$, i.e. the numbers $-2(n+1)$ with $n$ a natural number, and $s=1$ is the unique pole.
--
--   This theorem states that every other zero lies in the open **critical strip**: if $\zeta(s)=0$, $s$ is not of the form $-2(n+1)$ for a natural number $n$, and $s\neq 1$, then
--
--   $$0<\operatorname{Re} s<1.$$
--
--   The statement is unconditional and is the standard localisation of the nontrivial zeros. It is the step that turns the Riemann hypothesis, as stated for arbitrary zeros of $\zeta$ with the two exceptional families removed, into a statement about zeros in the strip, where the functional equation and the theory of $\zeta$ on $0<\operatorname{Re} s<1$ apply. Any argument about nontrivial zeros can use it to obtain the strip hypotheses for free.
--
--   **Formalization Note.** `riemannZeta` is Mathlib's zeta function, and the exclusion of the trivial zeros and of the pole is phrased exactly as in Mathlib's `RiemannHypothesis` predicate, so this lemma applies verbatim to the hypotheses of that predicate.
-- source:
--   Standard localisation of the nontrivial zeros of the Riemann zeta function: https://en.wikipedia.org/wiki/Riemann_zeta_function#Zeros,_the_critical_line,_and_the_Riemann_hypothesis ('the functional equation together with the non-vanishing of ζ on Re(s) ≥ 1 shows that the only zeros with Re(s) ≤ 0 are the trivial zeros −2, −4, −6, …, so all other zeros lie in the critical strip 0 < Re(s) < 1'). Ingredients available in Mathlib: `riemannZeta_one_sub` (functional equation) and `riemannZeta_ne_zero_of_one_le_re` (non-vanishing on Re(s) ≥ 1).

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex

theorem zeta_nontrivial_zero_mem_critical_strip (s : ℂ) (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by sorry
