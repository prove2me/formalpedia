-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_theorem_2
-- name    : XinMartingaleInventory.Minimax.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:35.661474+00:00
-- url     : https://prove2.me/theorems/e169e22d-0633-42cf-9659-343dadbfad66
-- title:
--   Theorem 2 — Dynamic-programming verification
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals. The selectors in this statement are arbitrary simultaneous Bellman optimizers selected as on p.11.
--
--   Theorem 2. For all strictly positive U,b ∈ Q⁺, T ≥ 1, and μ,x₀ ∈ [0,U]ℚ, π̂* is an optimal policy for Problem 2.4, and Q̂* ∈ arg max_{Q∈MAR} E_Q[∑_{t=1}^T C_t^{π̂*}]. Furthermore, V̂^T(x₀,μ) is the optimal value of Problem 2.4.
--
--   Differences from the source:
--   - encoding: probability laws on rational vectors and their expectations → nonnegative real atom masses with HasSum equal to one, and countable weighted sums; reason: rational finite histories are countable and bounded observables are summable; no finite-support restriction
--   - encoding: chronological finite histories and one-based periods → reverse-order lists and zero-based cost indices; policies extend by zero outside their valid histories; reason: this is a bijective representation of the same history rules; canonical extension preserves the uniqueness claim
--   - reading: the selector is displayed on nonnegative stocks but later applied to potentially negative pre-order stock → apply the chosen selector at max(y,0) when pre-order stock is y; reason: the constrained feasible action set for y≤0 equals the set at zero, without restricting backlogs
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Theorem 2, p.11 (PDF p.11)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem theorem_2 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (μ x₀ : ℚ) (hμ : μ ∈ Set.Icc 0 U) (hx₀ : x₀ ∈ Set.Icc 0 U) (φ : StockSelector) (q : LawSelector) (hsel : validSelectors U b T φ q) :
    optimalPolicy U b x₀ T (martingaleLaws U μ T) (genericPolicy U φ T x₀ μ) ∧
    worstLaw b T (martingaleLaws U μ T) (genericPolicy U φ T x₀ μ) (genericDemand U φ q T x₀ μ) ∧
    bellmanV U b T x₀ μ = minimaxValue U b x₀ T (martingaleLaws U μ T) := by sorry

end XinMartingaleInventory.Minimax
