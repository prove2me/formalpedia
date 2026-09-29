-- Prove2me | Theorems.Thm_zeta_ne_zero_of_half_lt_re
-- name    : zeta_ne_zero_of_half_lt_re
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-06T10:57:08.566353+00:00
-- url     : https://prove2.me/theorems/41e752a5-420b-44b5-8722-d1ad2a397260
-- title:
--   $\zeta$ has no zeros in the half-plane $\operatorname{Re} s>1/2$
-- statement:
--   Let $\zeta$ denote the Riemann zeta function. The assertion is that $\zeta$ has no zero to the right of the critical line:
--
--   $$\operatorname{Re} s>\tfrac12 \;\Longrightarrow\; \zeta(s)\neq 0.$$
--
--   This is the **half-plane form of the Riemann hypothesis**, and it is open. For $\operatorname{Re} s\ge 1$ it is a theorem (the non-vanishing of $\zeta$ on the line $\operatorname{Re} s=1$ underlying the prime number theorem, available in Mathlib as `riemannZeta_ne_zero_of_one_le_re`); the content is the range $\tfrac12<\operatorname{Re} s<1$.
--
--   Its value as a target is that, combined with the localisation of the nontrivial zeros in the critical strip and the reflection symmetry $s\mapsto 1-s$ coming from the functional equation, it yields the Riemann hypothesis in the form stated by Mathlib's `RiemannHypothesis` predicate: a zero-free open half-plane on one side of the critical line forces every nontrivial zero onto the line. Stating it as a zero-free region, rather than as a statement about the real parts of zeros, also matches the way zero-density and zero-free-region results in analytic number theory are formulated, so partial progress can be phrased against it directly.
-- source:
--   The Riemann hypothesis in its zero-free half-plane form: https://en.wikipedia.org/wiki/Riemann_hypothesis ('the Riemann hypothesis is equivalent to the statement that ζ(s) has no zeros with Re(s) > 1/2'). Equivalent to the mission goal theorem `riemann_hypothesis` (Mathlib's `RiemannHypothesis`).

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex

theorem zeta_ne_zero_of_half_lt_re (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by sorry
