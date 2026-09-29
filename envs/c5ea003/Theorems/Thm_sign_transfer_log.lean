-- Prove2me | Theorems.Thm_sign_transfer_log
-- name    : sign_transfer_log
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T18:22:54.651297+00:00
-- url     : https://prove2.me/theorems/888b0557-dd2e-4684-85f0-222fb801cdc0
-- title:
--   Sign transfer from the log-density difference to the density difference
-- statement:
--   **Sign-transfer from the log-density difference to the density difference (Siegel 2001, Theorem 2.1 / 2.2, p.5-6).** For a strictly positive density $f>0$, the sign of $g(x)=f(x)-f(2\mu-x)$ coincides with the sign of $\varphi(x)=\log f(x)-\log f(2\mu-x)$ (since $\log$ is strictly increasing on $(0,\infty)$). Hence a single-crossing point $c$ for $\varphi$ — $\varphi\le 0$ on $[0,c]$ and $\varphi\ge 0$ on $[c,\mu]$ — yields the same sign data $g\le0$ on $[0,c]$, $g\ge0$ on $[c,\mu]$. Siegel works the unimodality argument on $\log f$ (its derivative is rational in $e^{-\lambda t}$ with a quadratic numerator), then transfers back to $f$; this lemma is exactly that transfer.
-- source:
--   A. Siegel, "Median Bounds and their Application", J. Algorithms 38:184-236, 2001, Theorem 2.1 / Theorem 2.2, p.5-6 (the argument is carried on the log-density and transferred to the density via monotonicity of log).

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
set_option autoImplicit false
open Set

theorem sign_transfer_log
    (f : ℝ → ℝ) (μ c : ℝ)
    (hf : ∀ x, 0 < f x)
    (hL : ∀ x ∈ Icc (0:ℝ) c, Real.log (f x) - Real.log (f (2*μ - x)) ≤ 0)
    (hR : ∀ x ∈ Icc c μ, 0 ≤ Real.log (f x) - Real.log (f (2*μ - x))) :
    (∀ x ∈ Icc (0:ℝ) c, f x - f (2*μ - x) ≤ 0) ∧
    (∀ x ∈ Icc c μ, 0 ≤ f x - f (2*μ - x)) := by sorry
