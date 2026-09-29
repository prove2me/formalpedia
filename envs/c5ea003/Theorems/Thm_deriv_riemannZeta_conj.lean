-- Prove2me | Theorems.Thm_deriv_riemannZeta_conj
-- name    : deriv_riemannZeta_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:07:43.497679+00:00
-- url     : https://prove2.me/theorems/643b8510-d23c-4a49-8a74-86cd8110f84f
-- title:
--   Conjugation symmetry of $\zeta'$: $\zeta'(\overline{s}) = \overline{\zeta'(s)}$
-- statement:
--   For every complex number $s$, the derivative of the Riemann zeta function satisfies the conjugation symmetry
--
--   $$\zeta'\left(\overline{s}\right) \;=\; \overline{\zeta'(s)},$$
--
--   where $\overline{z}$ denotes complex conjugation.
--
--   This is the derivative-level companion of the reflection identity $\overline{\zeta(\overline{s})} = \zeta(s)$: since conjugation is an (antiholomorphic) isometry, differentiating the reflected function transfers the symmetry from $\zeta$ to $\zeta'$. Together the two identities say that the pair $(\zeta, \zeta')$ is completely determined by its behaviour in the upper half-plane.
--
--   In the PNT+ project this lemma allows every bound on $\zeta'$ — such as the $O((\log t)^2)$ estimates near the $1$-line — proved for $t > 0$ to be transferred verbatim to $t < 0$, halving the case analysis in the zero-free region and contour-integration arguments.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaConj.lean#L69-L71

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by sorry
