-- Prove2me | Theorems.Thm_ZeroFreeBridge_sum_divisor_recenter_le_finsum
-- name    : ZeroFreeBridge.sum_divisor_recenter_le_finsum
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:52:47.074918+00:00
-- url     : https://prove2.me/theorems/b67a0bac-3457-45d6-8326-5de43166c5f1
-- title:
--   Comparison of centered and uncentered divisor counts
-- statement:
--   Let $c\in\mathbb C$, $R\in\mathbb R$, and $f(w)=\zeta(c+w)$. Suppose $\zeta$
--   is meromorphic on $B(c,R)$ and analytic near its closure, and $f$ is meromorphic
--   on $B(0,R)$. If $S$ is the finite support of the negative divisor of $f$ in the
--   latter disk, then
--   $$\sum_{u\in S}\operatorname{div}_{B(0,R)}f(u)\le
--   \sum{}^{\!f}_{\rho}\operatorname{div}_{\overline{B(c,R)}}\zeta(\rho).$$
--   The right side is the finite-support sum over the original closed disk.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaCountReconcile.lean#L43-L95

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
/- PHASE 4 (dVP frontier, item 2(i) — the count RECONCILIATION core): bound the recentred divisor
   sum (the Herglotz-sum zero count over `ball 0 R`) by the ζ finsum over `closedBall c₀ R`, which
   `zeta_zero_count_strip` then bounds by an O(log|c₀.im|) Jensen quantity.

   The gap `hAL` faces: its sum is `∑ over toFinset` of the RECENTRED divisor on `ball 0 R`, while
   the Jensen count is a finsum of `divisor ζ` on a `closedBall`.  This file bridges them (the hard
   discrete part; `finsum_le_finsum` is absent in Mathlib, so it is assembled from lower-level pieces):
     * `sum_divisor_recenter_eq_image` — pointwise translate (`divisor_comp_const_add_apply`) +
       shift-reindex (`Finset.sum_image`, `add_left_cancel` injective) ⟹ recentred sum = ζ sum over
       the shifted image `{c₀+u}`;
     * `sum_divisor_recenter_le_finsum` — `ball c₀ R = closedBall c₀ R` divisor on interior points
       (`divisor_apply` both sides = same order), then `image ⊆ finiteSupport` (compact-domain
       `locallyFinsuppWithin.finiteSupport`) + `Finset.sum_le_sum_of_subset_of_nonneg` (`divisor ≥ 0`)
       + `finsum_eq_finset_sum_of_support_subset` ⟹ `∑ ≤ ∑ᶠ divisor ζ (closedBall c₀ R)`.
   Chaining with `zeta_zero_count_strip` (inner `R`, outer `R' > R`) gives the O(L) `hcount` that
   `hAL_concrete` consumes.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.sum_divisor_recenter_le_finsum {c₀ : ℂ} {R : ℝ}
    (hf_mero : MeromorphicOn riemannZeta (ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (ball 0 R))
    (hf_ana_cl : AnalyticOnNhd ℂ riemannZeta (closedBall c₀ R))
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u))).Finite) :
    (∑ u ∈ hfin.toFinset, (divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u : ℤ))
      ≤ ∑ᶠ ρ, divisor riemannZeta (closedBall c₀ R) ρ := by sorry
