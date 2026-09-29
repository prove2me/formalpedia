-- Prove2me | Theorems.Thm_ResidueDial_accounting_gap
-- name    : ResidueDial.accounting_gap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:57:53.728697+00:00
-- url     : https://prove2.me/theorems/9ca1f4b3-8777-4251-baa3-8af7c126f52e
-- title:
--   The gap is real.
-- statement:
--   **The gap is real.**  The worst-case-in-phase cap `4/3` is strictly below the
--   expected-position barrier `2`, and the latter is approached: for every `ε > 0`
--   some balanced dial has expected-position speedup `> 2 - ε`, while *no* dial ever
--   has worst-case-in-phase speedup above `4/3`.
--
--   ```lean
--   theorem ResidueDial.accounting_gap(ε : ℝ) (hε : 0 < ε) :
--       (∀ θ : ℝ, speedup θ ≤ 4 / 3) ∧ (4 / 3 : ℝ) < 2 ∧
--         ∃ m : ℕ, 0 < m ∧ 2 - ε < avgSpeedup m m ∧ avgSpeedup m m < 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ResidueDial/Accounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ResidueDial/Accounting.lean#L192

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







/-! ## The accounting gap -/

theorem ResidueDial.accounting_gap(ε : ℝ) (hε : 0 < ε) :
    (∀ θ : ℝ, speedup θ ≤ 4 / 3) ∧ (4 / 3 : ℝ) < 2 ∧
      ∃ m : ℕ, 0 < m ∧ 2 - ε < avgSpeedup m m ∧ avgSpeedup m m < 2 := by sorry
