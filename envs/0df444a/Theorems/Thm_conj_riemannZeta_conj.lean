-- Prove2me | Theorems.Thm_conj_riemannZeta_conj
-- name    : conj_riemannZeta_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:07:33.393287+00:00
-- url     : https://prove2.me/theorems/0b1d5911-5e32-4774-b861-7918dbd5c729
-- title:
--   Reflection symmetry of the Riemann zeta function: $\overline{\zeta(\overline{s})} = \zeta(s)$
-- statement:
--   For every complex number $s$, the Riemann zeta function satisfies the conjugation symmetry
--
--   $$\overline{\zeta\left(\overline{s}\right)} \;=\; \zeta(s),$$
--
--   where $\overline{z}$ denotes complex conjugation. Equivalently, $\zeta$ commutes with reflection in the real axis: the value of $\zeta$ at the mirror point $\overline{s}$ is the mirror of the value at $s$.
--
--   For $\operatorname{Re}(s) > 1$ this is immediate from the Dirichlet series $\zeta(s) = \sum n^{-s}$, whose coefficients are real; the full statement extends the symmetry to all of $\mathbb{C}$ (including the continuation past the pole at $s = 1$) by the Schwarz reflection principle / uniqueness of analytic continuation. This is the standard "reality" property of $\zeta$: it forces the non-trivial zeros to come in conjugate pairs $\rho, \overline{\rho}$, and in the PNT+ project it lets bounds and zero-free-region statements proved for $t > 0$ be transferred automatically to $t < 0$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaConj.lean#L29-L64

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate

theorem conj_riemannZeta_conj (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by sorry
