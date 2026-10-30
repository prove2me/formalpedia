-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_17
-- name    : XinMartingaleInventory.Minimax.lemma_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:27.731624+00:00
-- url     : https://prove2.me/theorems/00b4ed77-8dae-4c96-9a3a-77eeddf81a68
-- title:
--   Lemma 17 — Pasting laws and policies
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals. The selectors in this statement are arbitrary simultaneous Bellman optimizers selected as on p.11.  The initial mean μ and initial stock x₀ belong to [0,U]∩ℚ.
--
--   Lemma 17. Given π ∈ Π, Q ∈ MAR_T, and t ∈ [1,T−1], there exists a unique probability measure Q^{π,t} ∈ MAR^π_t satisfying Q^{π,t}_{[T−t]} = Q_{[T−t]}. Similarly, given π ∈ Π and t ∈ [1,T−1], there exists a unique policy π^t ∈ Π_t satisfying x^π_{[T−t]} = x^{π^t}_{[T−t]}.
--
--   Differences from the source:
--   - encoding: probability laws on rational vectors and their expectations → nonnegative real atom masses with HasSum equal to one, and countable weighted sums; reason: rational finite histories are countable and bounded observables are summable; no finite-support restriction
--   - encoding: chronological finite histories and one-based periods → reverse-order lists and zero-based cost indices; policies extend by zero outside their valid histories; reason: this is a bijective representation of the same history rules; canonical extension preserves the uniqueness claim
--   - reading: the selector is displayed on nonnegative stocks but later applied to potentially negative pre-order stock → apply the chosen selector at max(y,0) when pre-order stock is y; reason: the constrained feasible action set for y≤0 equals the set at zero, without restricting backlogs
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 17, p.41 (PDF p.41)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_17 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (μ x₀ : ℚ) (hμ : μ ∈ Set.Icc 0 U) (hx₀ : x₀ ∈ Set.Icc 0 U) (φ : StockSelector) (q : LawSelector) (hsel : validSelectors U b T φ q) :
    (∀ π ∈ policies U x₀ T, ∀ Q ∈ martingaleLaws U μ T, ∀ t, 1 ≤ t → t < T →
      ∃! Q' : PathLaw, Q' ∈ restrictedLaws U μ x₀ T φ q π t ∧
        ∀ h, h.length = T-t → prefixMass Q' h = prefixMass Q h) ∧
    (∀ π ∈ policies U x₀ T, ∀ t, 1 ≤ t → t < T →
      ∃! π' : Policy, π' ∈ restrictedPolicies U μ x₀ T φ t ∧
        ∀ h, h.length < T-t → validHistory U h → π' h = π h) := by sorry

end XinMartingaleInventory.Minimax
