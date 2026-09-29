-- Prove2me | Theorems.Thm_siegel_logdensity_bridge
-- name    : siegel_logdensity_bridge
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T19:04:49.762411+00:00
-- url     : https://prove2.me/theorems/39f88bdb-7608-4d07-8788-02ada9cef795
-- title:
--   Log of the Siegel waiting-time density splits additively
-- statement:
--   For the explicit Siegel waiting-time density $f(t)=K\,(1-e^{-\lambda t})^{m}\,(e^{-\lambda t})^{p}$ (with $K>0$ and natural-number exponents $m=$ `mNat`, $p$), the logarithm splits additively on the region where $1-e^{-\lambda t}>0$: $$\log f(t) = \big(m\,\log(1-e^{-\lambda t}) - p\,\lambda t\big) + \log K.$$ This is the algebraic bridge between the density form used for FTC/CDF computations and the log-density $G(t)=m\,\log(1-e^{-\lambda t})-p\,\lambda t$ whose symmetrized difference Siegel analyses. Proof: `Real.log_mul` to split the product, `Real.log_pow` for the natural powers, and `Real.log_exp` for $\log e^{-\lambda t}=-\lambda t$. Source: Siegel, 'Median Bounds and their Application', J. Algorithms 38:184-236, 2001, Theorem 2.2 / §2.1.1 (the waiting-time density).
-- source:
--   Siegel 2001, J. Algorithms 38:184-236, Thm 2.2 / §2.1.1 (waiting-time density); log algebra.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem siegel_logdensity_bridge (lam K : ℝ) (p : ℕ) (mNat : ℕ) (t : ℝ) (hK : 0 < K) (hpos : 0 < 1 - Real.exp (-lam * t)) : Real.log (K * (1 - Real.exp (-lam * t)) ^ mNat * (Real.exp (-lam * t)) ^ p) = ((mNat : ℝ) * Real.log (1 - Real.exp (-lam * t)) - (p : ℝ) * (lam * t)) + Real.log K := by sorry
