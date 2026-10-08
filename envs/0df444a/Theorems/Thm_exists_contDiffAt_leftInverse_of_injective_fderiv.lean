-- Prove2me | Theorems.Thm_exists_contDiffAt_leftInverse_of_injective_fderiv
-- name    : exists_contDiffAt_leftInverse_of_injective_fderiv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T17:23:13.788978+00:00
-- url     : https://prove2.me/theorems/1157f3f4-3fc6-486f-aeeb-0ccf430602f0
-- title:
--   An immersion has a smooth local left inverse
-- statement:
--   Let $E,F$ be finite-dimensional real normed spaces and $e:E\to F$ a map that is $C^\infty$ at $p$ with injective differential $De(p)$. Then $e$ has a smooth local left inverse at $p$: there is $g:F\to E$, $C^\infty$ at $e(p)$, with $g(e(q))=q$ for all $q$ in a neighborhood of $p$.
--   Proof idea: choose a linear left inverse $L$ of $De(p)$. Then $L\circ e$ has derivative $\mathrm{id}_E$ at $p$, so the inverse function theorem gives a smooth local inverse $\phi$ of $L\circ e$ at $p$. Take $g=\phi\circ L$.
-- source:
--   Standard (inverse function theorem applied to a linear left inverse of the differential); used for the lift step of Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped ContDiff Topology

theorem exists_contDiffAt_leftInverse_of_injective_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : E → F} {p : E} (he : ContDiffAt ℝ ∞ e p)
    (hinj : Function.Injective (fderiv ℝ e p)) :
    ∃ g : F → E, ContDiffAt ℝ ∞ g (e p) ∧ ∀ᶠ q in 𝓝 p, g (e q) = q := by sorry
