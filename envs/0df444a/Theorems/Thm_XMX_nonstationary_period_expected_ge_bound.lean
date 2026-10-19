-- Prove2me | Theorems.Thm_XMX_nonstationary_period_expected_ge_bound
-- name    : XMX.nonstationary_period_expected_ge_bound
-- status  : Open
-- author  : @fizzyinc3
-- created : 2026-10-18T11:37:42.715713+00:00
-- url     : https://prove2.me/theorems/74f0e510-504e-4ffc-b028-657d9c9d3af0
-- title:
--   Xie–Ma–Xin: horizon-independent generalization bound for each period
-- statement:
--   Let demands take values in $[0,U]$ and let the nonstationary base-stock levels lie in $[0,(L+1)U]$. Fix any period $L+k+1$, with $0\le k<T$, and regard its holding and backlog cost as a function of the whole demand trajectory and the policy vector. There is one absolute constant $C>0$ such that, from $N>0$ independent whole trajectories with any joint demand law, the expected one-sided uniform generalization error of this single-period cost class is at most
--
--   $$C(L+1)U/\sqrt N.$$
--
--   The same constant works for every period, horizon, lead time, positive support bound, cost coefficients $h,b\in[0,1]$, and demand distribution. Dependence between periods within a trajectory is allowed; fixed ordering cost is zero. This is the periodwise statistical estimate in Section 8.6 of Xie–Ma–Xin, before averaging over periods. It is the remaining empirical-process obligation in a reduction of the mission's Corollary 4.10; it does not assume an ERM selector or an optimal population policy.
-- source:
--   Y. Xie, W. Ma, L. Xin, VC Theory for Inventory Policies, arXiv:2404.11509v3, Section 8.6 proof of Corollary 4.10, Eqs. (8.15)–(8.17) and the uniform per-period fat-shattering estimate of Theorem 4.9. https://arxiv.org/html/2404.11509v3#S8.SS6

import Definitions.Def_XMX_NonstationaryInventory

set_option autoImplicit false
open MeasureTheory

namespace XMX

/-- The single-period empirical-process estimate used in the proof of Corollary 4.10. -/
theorem nonstationary_period_expected_ge_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T L N : ℕ), 0 < T → 0 < N →
      ∀ (U h b : ℝ), 0 < U → h ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (μ : Measure (Demand T L U)) [IsProbabilityMeasure μ], ∀ k : Fin T,
      expectedGE N μ (fun (S : Levels T L U) (d : Demand T L U) =>
        cost h b (inventory T L U S d k - (d ⟨L + k, by omega⟩ : ℝ))) ≤
        C * (((L : ℝ) + 1) * U) / Real.sqrt N := by sorry

end XMX
