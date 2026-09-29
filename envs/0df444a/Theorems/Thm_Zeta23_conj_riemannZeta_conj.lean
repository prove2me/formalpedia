-- Prove2me | Theorems.Thm_Zeta23_conj_riemannZeta_conj
-- name    : Zeta23_conj_riemannZeta_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:41:01.782555+00:00
-- url     : https://prove2.me/theorems/e93410c9-f0b1-4523-9708-4232fda5211d
-- title:
--   Reflection symmetry $\overline{\zeta(\bar s)} = \zeta(s)$
-- statement:
--   For every complex number $s$, the Riemann zeta function (Mathlib's `riemannZeta`, defined on all of $\mathbb{C}$ with $\zeta(1)$ given by a junk value) satisfies the Schwarz reflection identity
--   $$\overline{\zeta(\bar s)} \;=\; \zeta(s),$$
--   where the bar is complex conjugation. For $\operatorname{Re} s > 1$ this is immediate from the Dirichlet series with real coefficients; the identity extends to all $s \ne 1$ by the identity theorem for analytic functions on the connected set $\mathbb{C} \setminus \{1\}$, and is checked directly at $s = 1$ for Mathlib's convention $\zeta(1) = (\gamma_E - \log(4\pi))/2$, which is real.
--
--   A direct consequence is that the nontrivial zeros of $\zeta$ are symmetric under $s \mapsto \bar s$. The theorem lives in `Zeta23.FromPNTPlus.ZetaConj` (ported from the PrimeNumberTheoremAnd project) and is consumed by `Zeta23.RvM.horizontal_fold` and `Zeta23.RvM.vertical_fold`: the folding steps of the argument-principle contour in the Riemann–von Mangoldt zero-counting development, which reduce the rectangular contour integral to its right half.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/ZetaConj.lean#L43-L78

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate

theorem Zeta23_conj_riemannZeta_conj (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by sorry
