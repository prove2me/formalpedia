-- Prove2me | Theorems.Thm_scalar_convergence
-- name    : scalar_convergence
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T12:15:07.311403+00:00
-- url     : https://prove2.me/theorems/327bde27-e1e3-466a-9b71-6efea53fe5e8
-- title:
--   scalar convergence
-- statement:
--   Generic scalar convergence lemma behind the subgradient-method arguments. Let d be a nonnegative sequence with d (k+1) <= d k + s k and s k -> 0. Suppose that for every eps > 0 there is c > 0 such that eventually, whenever eps <= d k, the square d (k+1)^2 drops below d k^2 by at least c * w k, where w k > 0 and the partial sums of w diverge. Then d k -> 0.

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Topology
open scoped RealInnerProductSpace
open ShorNonsmooth.Stochastic
open ShorNonsmooth.SubgradMethod

theorem scalar_convergence (d w s : ℕ → ℝ)
    (hd : ∀ k, 0 ≤ d k) (hw : ∀ k, 0 < w k)
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, w k) atTop atTop)
    (hs : Tendsto s atTop (𝓝 0))
    (hjump : ∀ᶠ k in atTop, d (k+1) ≤ d k + s k)
    (hdesc : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in atTop, ε ≤ d k → d (k+1)^2 ≤ d k^2-c*w k) :
    Tendsto d atTop (𝓝 0) := by sorry
