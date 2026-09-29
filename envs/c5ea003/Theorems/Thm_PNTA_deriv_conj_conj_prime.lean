-- Prove2me | Theorems.Thm_PNTA_deriv_conj_conj_prime
-- name    : PNTA.deriv_conj_conj_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T06:06:06.809004+00:00
-- url     : https://prove2.me/theorems/53458de8-456d-4ef3-a691-fa141a304c00
-- title:
--   Derivative of the Schwarz-reflected function: $\overline{f(\bar z)}$
-- statement:
--   The Schwarz reflection of a function differentiates to the reflection of its derivative.
--
--   For any $f : \mathbb{C} \to \mathbb{C}$ and any point $p$,
--   $$\frac{d}{dz}\Big[\, \overline{f(\bar z)} \,\Big]_{z = \bar p} \;=\; \overline{f'(p)} .$$
--
--   Conjugation is an anti-holomorphic involution, and conjugating both the argument and the value composes two of them into a holomorphic operation; the two conjugations cancel in the difference quotient, leaving the conjugate of the original derivative. This identity is the engine behind every "reflect across the real axis" symmetry statement, including the conjugation symmetry of $\zeta'/\zeta$.
--
--   **Formalization Note** No differentiability hypothesis is needed: at points where $f$ is not differentiable both sides take the same junk value.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaConj.lean#L24-L29

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate

theorem PNTA.deriv_conj_conj_prime (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by sorry
