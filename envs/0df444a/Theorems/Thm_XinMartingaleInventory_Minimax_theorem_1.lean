-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_theorem_1
-- name    : XinMartingaleInventory.Minimax.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:02.584572+00:00
-- url     : https://prove2.me/theorems/08b760fb-eb01-43b2-8698-283cd30046f3
-- title:
--   Theorem 1 — Independent-demand benchmark
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Theorem 1 ([119]). For all strictly positive U,b ∈Q+,T ≥1, and µ,x0 ∈[0,U]Q, Problem 2.1
--   always has an optimal base-stock policy π∗, in which the associated base-stock constants {x∗
--   t ,t ∈
--   [1,T]} satisfy x∗
--   t = χIND(µ,U,b) for all t ∈[1,T]. If x0 ≤χIND(µ,U,b), the optimal value of Prob-
--   lem 2.1 equals OptT
--   IND(µ,U,b); and for all x0 ∈[0,U], the product measure s.t. all marginals are
--   distributed according to law Dµ belongs to arg maxQ∈IND EQ[PT
--   t=1 Cπ∗
--   t ]. Furthermore, the DP for-
--   mulation (2.2) - (2.3) can be used to compute these optimal policies, distributions, and values. In
--   particular, for all x0,x,µ ∈[0,U]Q, V T(x0,µ) is the optimal value of Problem 2.1, Dµ ∈QT (x,µ),
--   and max(x,χIND(µ,U,b))
--   ∈ΦT(x,µ).
--
--   Differences from the source:
--   - encoding: probability laws on rational vectors and their expectations → nonnegative real atom masses with HasSum equal to one, and countable weighted sums; reason: rational finite histories are countable and bounded observables are summable; no finite-support restriction
--   - encoding: chronological finite histories and one-based periods → reverse-order lists and zero-based cost indices; policies extend by zero outside their valid histories; reason: this is a bijective representation of the same history rules; canonical extension preserves the uniqueness claim
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Theorem 1, p.9 (PDF p.9)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem theorem_1 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (μ x₀ : ℚ) (hμ : μ ∈ Set.Icc 0 U) (hx₀ : x₀ ∈ Set.Icc 0 U) :
    optimalPolicy U b x₀ T (independentLaws U μ T) (independentPolicy U b x₀ μ T) ∧
    (∀ h, validDecisionHistory U T h → independentPolicy U b x₀ μ T h =
      max (preStock x₀ (independentPolicy U b x₀ μ T) h) (independentThreshold U b μ)) ∧
    (x₀ ≤ independentThreshold U b μ →
      minimaxValue U b x₀ T (independentLaws U μ T) = independentValue U b μ T) ∧
    worstLaw b T (independentLaws U μ T) (independentPolicy U b x₀ μ T) (independentDemand U μ T) ∧
    independentV U b μ T x₀ = minimaxValue U b x₀ T (independentLaws U μ T) ∧
    (∀ x ∈ Set.Icc 0 U,
      endpointLaw U μ ∈ independentMax U b μ T x ∧
      max x (independentThreshold U b μ) ∈ independentMin U b μ T x) := by sorry

end XinMartingaleInventory.Minimax
