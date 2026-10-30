-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_theorem_3
-- name    : XinMartingaleInventory.Minimax.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:23.330517+00:00
-- url     : https://prove2.me/theorems/5ee631b1-c14a-4765-a029-0bc37b8fd145
-- title:
--   Theorem 3 — Closed-form minimax policy, worst-case demand and optimal value
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.  The initial mean μ and initial stock x₀ belong to [0,U]∩ℚ.
--
--   Theorem 3. For all t ∈ [1,T], and all x,d ∈ [0,U]ℚ, max(x,χ^t_MAR(d,U,b)) ∈ Φ̂^t(x,d), and we may set Φ̄^t_{x,d} = max(x,χ^t_MAR(d,U,b)). Thus an optimal policy π̂* for Problem 2.4 is given as follows. x̂*_1 = max(x₀,χ^T_MAR(μ,U,b)). For t ∈ [1,T−1],
--   x̂*_{t+1}(d_[t]) = max(x̂*_t(d_[t−1]) − d_t,χ^{T−t}_MAR(d_t,U,b)).
--   Similarly, q^t_{x,d} ∈ Q̂^t(x,d), and we may set Q̄^t_{x,d} = q^t_{x,d}. Thus a worst-case (at optimality) distribution Q̂* ∈ arg max_{Q∈MAR} E_Q[∑_{t=1}^T C_t^{π̂*}] may be given as follows. Q̂*_1 = q^T_{x̂*_1,μ}. For t ∈ [1,T−1] and d ∈ supp(Q̂*_[t]),
--   Q̂*_{t+1|d} = q^{T−t}_{x̂*_{t+1}(d),d_t}.
--   Furthermore, for all x₀ ≤ β^T_μ, the optimal value of Problem 2.4 equals Opt^T_MAR(μ,U,b).
--
--   Differences from the source:
--   - encoding: probability laws on rational vectors and their expectations → nonnegative real atom masses with HasSum equal to one, and countable weighted sums; reason: rational finite histories are countable and bounded observables are summable; no finite-support restriction
--   - encoding: chronological finite histories and one-based periods → reverse-order lists and zero-based cost indices; policies extend by zero outside their valid histories; reason: this is a bijective representation of the same history rules; canonical extension preserves the uniqueness claim
--   - encoding: real-variable formulas with rational primitives and integer threshold indices → rational A and B cast into real formulas, with finite interval-indicator sums selecting integer indices; reason: the interval selector is unique on the stated domain, including right-closed A intervals, left-closed B intervals through index n, and index minus one
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Theorem 3, p.13 (PDF p.13)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem theorem_3 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (μ x₀ : ℚ) (hμ : μ ∈ Set.Icc 0 U) (hx₀ : x₀ ∈ Set.Icc 0 U) :
    (∀ n, 1 ≤ n → n ≤ T → ∀ x ∈ Set.Icc 0 U, ∀ d ∈ Set.Icc 0 U,
      max x (beta U b n d) ∈ bellmanMin U b n x d ∧
      explicitLaw U b n x d ∈ bellmanMax U b n x d) ∧
    optimalPolicy U b x₀ T (martingaleLaws U μ T) (explicitPolicy U b x₀ μ T) ∧
    worstLaw b T (martingaleLaws U μ T) (explicitPolicy U b x₀ μ T) (optimalDemand U b x₀ μ T) ∧
    (conditionalMass (optimalDemand U b x₀ μ T) [] =
      explicitLaw U b T (max x₀ (beta U b T μ)) μ) ∧
    (∀ h, 1 ≤ h.length → h.length < T → 0 < prefixMass (optimalDemand U b x₀ μ T) h →
      conditionalMass (optimalDemand U b x₀ μ T) h =
        explicitLaw U b (T-h.length) (explicitPolicy U b x₀ μ T h) (previousDemand μ h)) ∧
    (x₀ ≤ beta U b T μ → minimaxValue U b x₀ T (martingaleLaws U μ T) = explicitValue U b T μ) := by sorry

end XinMartingaleInventory.Minimax
