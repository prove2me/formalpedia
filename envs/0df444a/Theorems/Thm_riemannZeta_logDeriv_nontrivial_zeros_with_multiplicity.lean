-- Prove2me | Theorems.Thm_riemannZeta_logDeriv_nontrivial_zeros_with_multiplicity
-- name    : riemannZeta_logDeriv_nontrivial_zeros_with_multiplicity
-- status  : Open
-- author  : @BrunoDCDO
-- created : 2026-10-03T18:43:42.802851+00:00
-- url     : https://prove2.me/theorems/5205e2ba-912b-4787-a376-33b6359005de
-- title:
--   The regularized zero expansion of the logarithmic derivative of zeta
-- statement:
--   Let $Z=\{\rho\in\mathbb C:0<\operatorname{Re}\rho<1,\ \zeta(\rho)=0\}$ be the set of distinct nontrivial zeros of the Riemann zeta function. For $\rho\in Z$, let $m_\rho$ be its order of vanishing. Let $\gamma$ be the Euler-Mascheroni constant, and let $\Psi=\Gamma'/\Gamma$ be the digamma function.
--
--   For every $s\in\mathbb C$ with $\operatorname{Re}s>0$, $s\ne1$, and $\zeta(s)\ne0$, the regularized zero sum converges absolutely:
--
--   $$\sum_{\rho\in Z}\left|m_\rho\left(\frac1{s-\rho}+\frac1\rho\right)\right|<\infty.$$
--
--   Moreover,
--
--   $$\frac{\zeta'(s)}{\zeta(s)}=\log(2\pi)-1-\frac\gamma2-\frac1{s-1}-\frac12\Psi\!\left(\frac s2+1\right)+\sum_{\rho\in Z}m_\rho\left(\frac1{s-\rho}+\frac1\rho\right).$$
--
--   This expansion expresses the logarithmic derivative in terms of its pole, the gamma factor, and the nontrivial zeros counted with their actual multiplicities. Absolute convergence makes the sum independent of an enumeration of the zeros. The identity is the form recorded by Rosser and Schoenfeld (1975), page 246, equations (1.11)-(1.13), on the domain stated here.
--
--   **Formalization note.** The sum is indexed by the subtype of nontrivial zeros of `riemannZeta`; its integer weight is the finite meromorphic order of that same function. The digamma function is Mathlib's `Complex.digamma`.
-- source:
--   J. Barkley Rosser and Lowell Schoenfeld, Sharper Bounds for the Chebyshev Functions theta(x) and psi(x), Mathematics of Computation 29 (129), January 1975, pp. 243-269, DOI 10.1090/S0025-5718-1975-0457373-7, https://doi.org/10.1090/S0025-5718-1975-0457373-7. Identity, constant, and regularized zero sum: p. 246, equations (1.11)-(1.13). The present statement gives this identity for Re(s)>0, s≠1, and ζ(s)≠0 and explicitly asserts absolute convergence.

import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Tactic
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem riemannZeta_logDeriv_nontrivial_zeros_with_multiplicity (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    Summable (fun ρ : {ρ : ℂ // 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0} =>
      ‖((meromorphicOrderAt riemannZeta (ρ : ℂ)).untop₀ : ℂ) *
        (1 / (s - (ρ : ℂ)) + 1 / (ρ : ℂ))‖) ∧
    deriv riemannZeta s / riemannZeta s =
      Complex.log (2 * (Real.pi : ℂ)) - 1 - (Real.eulerMascheroniConstant : ℂ) / 2 -
      1 / (s - 1) - Complex.digamma (s / 2 + 1) / 2 +
      ∑' ρ : {ρ : ℂ // 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0},
        ((meromorphicOrderAt riemannZeta (ρ : ℂ)).untop₀ : ℂ) *
          (1 / (s - (ρ : ℂ)) + 1 / (ρ : ℂ)) := by sorry
