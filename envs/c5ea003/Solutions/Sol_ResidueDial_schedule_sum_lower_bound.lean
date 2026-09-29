-- Prove2me | solution 1 for ResidueDial.schedule_sum_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:56:16.822271+00:00
-- url     : https://prove2.me/submissions/9d7ac1df-88dc-4ba8-8742-9adb79904fdb

-- Sol generated from Cryptography/ResidueDial/Accounting.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Accounting
import Definitions.Def_Cryptography_ResidueDial_Core
import Theorems.Thm_ResidueDial_sum_ge_triangular

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



open ResidueDial in
theorem solution(K : Finset α) (posIn posOut : α → ℤ)
    (hInjIn : Set.InjOn posIn K) (hIn1 : ∀ t ∈ K, 1 ≤ posIn t)
    (hInjOut : Set.InjOn posOut ((univ : Finset α) \ K))
    (hOut1 : ∀ t ∈ (univ : Finset α) \ K, 1 ≤ posOut t) :
    (K.card : ℤ) * (K.card + 1)
        + (((univ : Finset α) \ K).card : ℤ) * ((((univ : Finset α) \ K).card : ℤ) + 1)
      ≤ 2 * scheduleTotal K posIn posOut := by
  classical
  have hsplit : scheduleTotal K posIn posOut
      = (∑ t ∈ K, posIn t) + ∑ t ∈ (univ : Finset α) \ K, posOut t := by
    have hf1 : (univ : Finset α).filter (fun x => x ∈ K) = K := by ext x; simp
    have hf2 : (univ : Finset α).filter (fun x => x ∉ K) = (univ : Finset α) \ K := by
      ext x; simp
    rw [scheduleTotal, Finset.sum_ite, hf1, hf2]
  have h1 := sum_ge_triangular K posIn hInjIn hIn1
  have hInjOut' : Set.InjOn posOut (((univ : Finset α) \ K : Finset α) : Set α) := by
    intro x hx y hy hxy
    exact hInjOut (by simpa using hx) (by simpa using hy) hxy
  have h2 := sum_ge_triangular ((univ : Finset α) \ K) posOut hInjOut' hOut1
  rw [hsplit]
  linarith
