-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_theorem_8
-- name    : XinMartingaleInventory.Minimax.theorem_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:11.117801+00:00
-- url     : https://prove2.me/theorems/6acab8ce-1dc0-485d-bbb6-ba3f04defdca
-- title:
--   Theorem 8 — Five backward-induction identities
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals. The selectors in this statement are arbitrary simultaneous Bellman optimizers selected as on p.11.  The initial mean μ and initial stock x₀ belong to [0,U]∩ℚ.
--
--   Theorem 8. For all s ∈ [0,T−1], π ∈ Π_s, and Q ∈ MAR^π_s,
--   E_Q[∑_{t=T−s}^T C^π_t] = ∑_{q∈supp(Q_{[T−s−1]})} [∑_{z∈[0,U]ℚ} f̂^{s+1}(x^π_{T−s}(q),z)Q_{T−s|q}(z)]Q_{[T−s−1]}(q). (7.32)
--   For all s ∈ [0,T−1], π ∈ Π_s, and Q ∈ MAR^π_{s+1},
--   E_Q[∑_{t=T−s}^T C^π_t] = ∑_{q∈supp(Q_{[T−s−1]})} ĝ^{s+1}(x^π_{T−s}(q),q_{T−s−1})Q_{[T−s−1]}(q). (7.33)
--   For all s ∈ [0,T−1] and π ∈ Π_s,
--   sup_{Q∈MAR} E_Q[∑_{t=1}^T C^π_t] = sup_{Q∈MAR^π_{s+1}} E_Q[∑_{t=1}^T C^π_t]. (7.34)
--   For all s ∈ [0,T−1], π ∈ Π_{s+1}, and Q ∈ MAR^π_{s+1},
--   E_Q[∑_{t=T−s}^T C^π_t] = ∑_{q∈supp(Q_{[T−s−1]})} V̂^{s+1}(y^π_{T−s}(q),q_{T−s−1})Q_{[T−s−1]}(q). (7.35)
--   For all s ∈ [0,T−1],
--   inf_{π∈Π} sup_{Q∈MAR} E_Q[∑_{t=1}^T C^π_t] = inf_{π∈Π_{s+1}} sup_{Q∈MAR} E_Q[∑_{t=1}^T C^π_t]. (7.36)
--
--   Differences from the source:
--   - encoding: probability laws on rational vectors and their expectations → nonnegative real atom masses with HasSum equal to one, and countable weighted sums; reason: rational finite histories are countable and bounded observables are summable; no finite-support restriction
--   - encoding: chronological finite histories and one-based periods → reverse-order lists and zero-based cost indices; policies extend by zero outside their valid histories; reason: this is a bijective representation of the same history rules; canonical extension preserves the uniqueness claim
--   - reading: the selector is displayed on nonnegative stocks but later applied to potentially negative pre-order stock → apply the chosen selector at max(y,0) when pre-order stock is y; reason: the constrained feasible action set for y≤0 equals the set at zero, without restricting backlogs
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Theorem 8, p.42 (PDF p.42)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem theorem_8 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (μ x₀ : ℚ) (hμ : μ ∈ Set.Icc 0 U) (hx₀ : x₀ ∈ Set.Icc 0 U) (φ : StockSelector) (q : LawSelector) (hsel : validSelectors U b T φ q) :
    (∀ s, s < T → ∀ π ∈ restrictedPolicies U μ x₀ T φ s,
      ∀ Q ∈ restrictedLaws U μ x₀ T φ q π s,
      expectation Q (tailCost b T π (T-s-1)) =
        prefixExpectation Q (T-s-1) (fun h =>
          expectation (conditionalMass Q h) (bellmanF U b (s+1) (π h)))) ∧
    (∀ s, s < T → ∀ π ∈ restrictedPolicies U μ x₀ T φ s,
      ∀ Q ∈ restrictedLaws U μ x₀ T φ q π (s+1),
      expectation Q (tailCost b T π (T-s-1)) =
        prefixExpectation Q (T-s-1) (fun h => bellmanG U b (s+1) (π h) (previousDemand μ h))) ∧
    (∀ s, s < T → ∀ π ∈ restrictedPolicies U μ x₀ T φ s,
      worstCost b T (martingaleLaws U μ T) π =
        worstCost b T (restrictedLaws U μ x₀ T φ q π (s+1)) π) ∧
    (∀ s, s < T → ∀ π ∈ restrictedPolicies U μ x₀ T φ (s+1),
      ∀ Q ∈ restrictedLaws U μ x₀ T φ q π (s+1),
      expectation Q (tailCost b T π (T-s-1)) =
        prefixExpectation Q (T-s-1) (fun h =>
          bellmanV U b (s+1) (preStock x₀ π h) (previousDemand μ h))) ∧
    (∀ s, s < T → minimaxValue U b x₀ T (martingaleLaws U μ T) =
      sInf ((worstCost b T (martingaleLaws U μ T)) '' restrictedPolicies U μ x₀ T φ (s+1))) := by sorry

end XinMartingaleInventory.Minimax
