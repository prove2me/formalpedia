-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_2
-- name    : XinMartingaleInventory.Minimax.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:14.393184+00:00
-- url     : https://prove2.me/theorems/fd65ca82-4f02-4f44-b1a0-0b8fcf88c995
-- title:
--   Lemma 2 — Attainment and simultaneous selectors
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Lemma 2. For all t ∈ [1,T], and x,d ∈ [0,U]ℚ, Q̂^t(x,d) ≠ ∅, Φ̂^t(x,d) ≠ ∅. Furthermore, it is possible to assign to every t ∈ [1,T], and x,d ∈ [0,U]ℚ, a measure Q̄^t_{x,d} ∈ Q̂^t(x,d); and rational number Φ̄^t_{x,d} ∈ Φ̂^t(x,d).
--
--   Differences from the source:
--   - encoding: probability laws on rational vectors and their expectations → nonnegative real atom masses with HasSum equal to one, and countable weighted sums; reason: rational finite histories are countable and bounded observables are summable; no finite-support restriction
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 2, p.11 (PDF p.11)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_2 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) :
    (∀ n, 1 ≤ n → n ≤ T → ∀ x ∈ Set.Icc 0 U, ∀ m ∈ Set.Icc 0 U,
      (bellmanMax U b n x m).Nonempty ∧ (bellmanMin U b n x m).Nonempty) ∧
    ∃ φ : StockSelector, ∃ q : LawSelector, validSelectors U b T φ q := by sorry

end XinMartingaleInventory.Minimax
