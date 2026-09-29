-- Prove2me | Theorems.Thm_ResidueDial_schedule_sum_lower_bound
-- name    : ResidueDial.schedule_sum_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:59:08.955866+00:00
-- url     : https://prove2.me/theorems/e6d50164-7673-45f2-b484-434a64eabbf3
-- title:
--   Optimality lemma.
-- statement:
--   **Optimality lemma.**  Whatever orders the algorithm chooses inside the two
--   branches of the dial reading, the total cost is at least the sum of the two
--   triangular numbers.  Hence no dial-aware scan can beat `avgSpeedup`.
--
--   ```lean
--   theorem ResidueDial.schedule_sum_lower_bound(K : Finset α) (posIn posOut : α → ℤ)
--       (hInjIn : Set.InjOn posIn K) (hIn1 : ∀ t ∈ K, 1 ≤ posIn t)
--       (hInjOut : Set.InjOn posOut ((univ : Finset α) \ K))
--       (hOut1 : ∀ t ∈ (univ : Finset α) \ K, 1 ≤ posOut t) :
--       (K.card : ℤ) * (K.card + 1)
--           + (((univ : Finset α) \ K).card : ℤ) * ((((univ : Finset α) \ K).card : ℤ) + 1)
--         ≤ 2 * scheduleTotal K posIn posOut := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ResidueDial/Accounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ResidueDial/Accounting.lean#L82

-- Thm stub generated from Cryptography/ResidueDial/Accounting.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Accounting
import Definitions.Def_Cryptography_ResidueDial_Core

/-!
# Two accountings of a dial-aware scan: `4/3` versus `2`

The cap proved in `Core.lean` is `4/3`, while the *asked* barrier in the
literature is `2`.  The discrepancy is not a mistake in either place: it is a
difference of **cost accounting**, and this file isolates it exactly.

* **Worst-case-in-phase accounting** (`Core.lean`).  A phase that scans `m`
  classes is charged `m`.  Exact law `1 - θ + θ²`, exact cap `4/3`
  (`speedup_le_four_thirds`), attained at `θ = 1/2`.

* **Expected-position accounting** (this file).  The scan is charged the
  *position* at which the target is found, the algorithm being allowed to
  reorder the classes freely inside each branch of the dial reading.  The
  optimal expected cost of a dial with blocks of sizes `k` and `j` is
  `(k(k+1) + j(j+1)) / (2(k+j))`, against a baseline `(k+j+1)/2`, giving
  `avgSpeedup k j = (k+j)(k+j+1) / (k(k+1) + j(j+1))`.

The main results:

* `schedule_sum_lower_bound` — the optimality lemma: *any* pair of scan orders
  compatible with the dial reading costs at least the triangular sums.  This is
  what makes `avgSpeedup` an upper bound over all strategies, not just the value
  of one strategy.
* `avgSpeedup_lt_two` — under expected-position accounting the barrier is `2`,
  **never attained**.
* `avgSpeedup_balanced`, `avgSpeedup_balanced_tendsto_two` — it is nevertheless
  sharp: at balanced blocks the value is `(2m+1)/(m+1) → 2`.
* `accounting_gap` — the two accountings genuinely differ: `4/3 < 2`, and for
  every `ε > 0` the expected-position speedup exceeds `2 - ε` for large enough
  balanced blocks, while the worst-case-in-phase speedup never exceeds `4/3`.

Moral (the self-caught error of the round): the provable universal constant in
the worst-case-in-phase framing is `4/3`, and `2` is only the *supremum* of a
different, more generous accounting — reporting `≤ 2` in the first framing would
have been a strictly weaker, and reporting `= 2` a false, claim.
-/

open ResidueDial

open Finset

/-! ## Optimality of the block schedules -/


variable {α : Type*} [Fintype α] [DecidableEq α]

theorem ResidueDial.schedule_sum_lower_bound(K : Finset α) (posIn posOut : α → ℤ)
    (hInjIn : Set.InjOn posIn K) (hIn1 : ∀ t ∈ K, 1 ≤ posIn t)
    (hInjOut : Set.InjOn posOut ((univ : Finset α) \ K))
    (hOut1 : ∀ t ∈ (univ : Finset α) \ K, 1 ≤ posOut t) :
    (K.card : ℤ) * (K.card + 1)
        + (((univ : Finset α) \ K).card : ℤ) * ((((univ : Finset α) \ K).card : ℤ) + 1)
      ≤ 2 * scheduleTotal K posIn posOut := by sorry
