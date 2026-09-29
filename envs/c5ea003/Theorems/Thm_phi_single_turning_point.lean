-- Prove2me | Theorems.Thm_phi_single_turning_point
-- name    : phi_single_turning_point
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T20:15:47.992174+00:00
-- url     : https://prove2.me/theorems/f619f3f8-3669-449a-adef-5ddcab28330f
-- title:
--   Siegel Theorem 2.2: $\varphi'$ has a single turning point
-- statement:
--   **Siegel 2001, Theorem 2.2 / §2.1.1 — the $\varphi'$ single-turning-point step.** For the waiting-time log-density $G(t)=m\log(1-e^{-\lambda t})-(N-m)\lambda t$ (the log of the Siegel density $f(t)=K(1-e^{-\lambda t})^m(e^{-\lambda t})^{N-m}$ up to an additive constant), set the symmetrized log-ratio $\varphi(t)=G(t)-G(2\mu-t)$. Under the mean condition $N<(N-m)e^{\lambda\mu}$ (equivalently $e^{\lambda\mu}>N/(N-m)$ — the regime where the waiting-time mean $\mu$ sits above the failure-reversal threshold, which is exactly the binomial-median case), the derivative $\varphi'$ is **positive then negative**: there exists a single interior maximum $a\in(0,\mu)$ with $\varphi'(t)>0$ for $t\in(0,a)$ and $\varphi'(t)<0$ for $t\in(a,\mu)$. Here $G'(s)=m\lambda e^{-\lambda s}/(1-e^{-\lambda s})-(N-m)\lambda$ and $\varphi'(t)=G'(t)+G'(2\mu-t)$. This unimodality of $\varphi$ drives Siegel's moustache argument in the non-degenerate case: $\mathrm{sign}\,\varphi'(t)=\mathrm{sign}\,Q(e^{\lambda t})$ where $Q(u)=(2N-m)u^2-2(N+(N-m)e^{2\lambda\mu})u+e^{2\lambda\mu}(2N-m)$ is an upward parabola with $Q(1)=m(e^{2\lambda\mu}-1)>0$ and $Q(e^{\lambda\mu})=-2e^{\lambda\mu}(e^{\lambda\mu}-1)((N-m)e^{\lambda\mu}-N)<0$, and $Q$ is strictly decreasing on $[1,e^{\lambda\mu}]$ (the point $e^{\lambda\mu}$ lies left of the vertex); the intermediate value theorem then yields the unique crossing.
-- source:
--   A. Siegel, 'Median Bounds and their Application', J. Algorithms 38:184-236 (2001), Theorem 2.2 and §2.1.1 (the waiting-time / moustache proof of the integer-mean binomial median, after Jogdeo-Samuels 1968). This is the φ'-sign (single interior maximum) step in the non-degenerate (failure-reversal) regime e^{λμ} > N/(N-m).

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.IntermediateValue

theorem phi_single_turning_point (lam m Nn mu : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hmN : m < Nn) (hmu : 0 < mu) (hmean : Nn < (Nn - m) * Real.exp (lam * mu)) : ∃ a ∈ Set.Ioo (0:ℝ) mu, (∀ t ∈ Set.Ioo (0:ℝ) a, HasDerivAt (fun y => (m * Real.log (1 - Real.exp (-lam * y)) - (Nn - m) * (lam * y)) - (m * Real.log (1 - Real.exp (-lam * (2*mu - y))) - (Nn - m) * (lam * (2*mu - y)))) (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) t ∧ 0 < (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam)))) ∧ (∀ t ∈ Set.Ioo a mu, HasDerivAt (fun y => (m * Real.log (1 - Real.exp (-lam * y)) - (Nn - m) * (lam * y)) - (m * Real.log (1 - Real.exp (-lam * (2*mu - y))) - (Nn - m) * (lam * (2*mu - y)))) (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) t ∧ (((m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)) + ((m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam))) < 0) := by sorry
