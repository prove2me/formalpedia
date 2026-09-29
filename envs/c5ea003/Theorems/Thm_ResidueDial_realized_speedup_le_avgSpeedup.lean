-- Prove2me | Theorems.Thm_ResidueDial_realized_speedup_le_avgSpeedup
-- name    : ResidueDial.realized_speedup_le_avgSpeedup
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:58:35.161617+00:00
-- url     : https://prove2.me/theorems/b8cca26a-6b2b-4d0d-9973-d028aa3aac54
-- title:
--   The expected-position bound on realized speedup.
-- statement:
--   **The expected-position bound on realized speedup.**  The baseline scan
--   costs `(n+1)/2` on average; a dial-aware scan costs `scheduleTotal / n`.  By the
--   optimality lemma the resulting speedup is at most `avgSpeedup k j`, so
--   `avgSpeedup` is an upper bound over *all* dial-aware strategies.
--
--   ```lean
--   theorem ResidueDial.realized_speedup_le_avgSpeedup(K : Finset α) (posIn posOut : α → ℤ)
--       (hInjIn : Set.InjOn posIn K) (hIn1 : ∀ t ∈ K, 1 ≤ posIn t)
--       (hInjOut : Set.InjOn posOut ((univ : Finset α) \ K))
--       (hOut1 : ∀ t ∈ (univ : Finset α) \ K, 1 ≤ posOut t)
--       (hn : 0 < Fintype.card α) :
--       ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) + 1))
--           / (2 * (scheduleTotal K posIn posOut : ℝ))
--         ≤ avgSpeedup K.card (((univ : Finset α) \ K).card) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ResidueDial/Accounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ResidueDial/Accounting.lean#L159

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



/-! ## The expected-position speedup -/

theorem ResidueDial.realized_speedup_le_avgSpeedup(K : Finset α) (posIn posOut : α → ℤ)
    (hInjIn : Set.InjOn posIn K) (hIn1 : ∀ t ∈ K, 1 ≤ posIn t)
    (hInjOut : Set.InjOn posOut ((univ : Finset α) \ K))
    (hOut1 : ∀ t ∈ (univ : Finset α) \ K, 1 ≤ posOut t)
    (hn : 0 < Fintype.card α) :
    ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) + 1))
        / (2 * (scheduleTotal K posIn posOut : ℝ))
      ≤ avgSpeedup K.card (((univ : Finset α) \ K).card) := by sorry
