-- Prove2me | Theorems.Thm_XiMultiplicityPublished_concrete_normalized_disk_factorization
-- name    : XiMultiplicityPublished.concrete_normalized_disk_factorization
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:57:48.893189+00:00
-- url     : https://prove2.me/theorems/caa0dce8-0819-4acb-a80e-90df9f6cc1fe
-- title:
--   Concrete xi: normalized finite zero factorization on every disk
-- statement:
--   Let \(\xi(s)=[1+s(s-1)\Lambda_0(s)]/2\) be the concrete entire completion of zeta and let \(R>0\). Let \(D_R\) be its divisor restricted to \(|s|<R\), extended by zero outside that disk, and let
--   \[P_R(s)=\prod_{\rho\in\operatorname{supp}D_R}(s-\rho)^{D_R(\rho)}.\]
--   The support is precisely the zeros of \(\xi\) in the disk; it is finite, and every exponent is the analytic multiplicity of that zero. Also \(P_R(0)\ne0\). There exists a function \(H_R\), analytic and nonvanishing in the disk, with \(H_R(0)=1\), such that
--   \[\frac{\xi(s)}{\xi(0)}=\frac{P_R(s)}{P_R(0)}H_R(s)\qquad(|s|<R).\]
--   This is a finite factorization of the actual xi function. The residual factor is retained explicitly; the theorem neither sets it equal to one nor asserts convergence to the normalized infinite Hadamard product. The disk and normalization are centered at \(s=0\), not at \(s=1/2\).
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. Continuation of PF28 and Branches 2/3 formalization, 2026-11-16. Classical results and countable generalization; no novelty or RH proof claimed. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem XiMultiplicityPublished.concrete_normalized_disk_factorization (R : ℝ) (hR : 0 < R) :
    let f : ℂ → ℂ := (fun s : ℂ => (1+s*(s-1)*completedRiemannZeta₀ s)/2)
    let D := MeromorphicOn.divisor f (Metric.ball 0 R)
    let P : ℂ → ℂ := ∏ᶠ z : ℂ, (fun w : ℂ => w-z) ^ (D z)
    D.support.Finite ∧
    D.support = Metric.ball 0 R ∩ {z | f z = 0} ∧
    (∀ z ∈ Metric.ball 0 R, D z = (analyticOrderNatAt f z : ℤ)) ∧
    P 0 ≠ 0 ∧
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (Metric.ball 0 R) ∧ H 0 = 1 ∧
      (∀ z ∈ Metric.ball 0 R, H z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 R, f z / f 0 = (P z / P 0) * H z) := by sorry
