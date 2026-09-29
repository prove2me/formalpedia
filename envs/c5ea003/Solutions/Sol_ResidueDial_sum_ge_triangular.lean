-- Prove2me | solution 1 for ResidueDial.sum_ge_triangular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:52:42.108413+00:00
-- url     : https://prove2.me/submissions/8142786d-d495-4a00-b812-d9a283cdce17

-- Sol generated from Cryptography/ResidueDial/Accounting.lean
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



open ResidueDial in
theorem solution{α : Type*} [DecidableEq α] (S : Finset α) (p : α → ℤ)
    (hinj : Set.InjOn p S) (h1 : ∀ t ∈ S, 1 ≤ p t) :
    (S.card : ℤ) * (S.card + 1) ≤ 2 * ∑ t ∈ S, p t := by
  classical
  set T : Finset ℤ := S.image p with hT
  have hcard : T.card = S.card :=
    Finset.card_image_of_injOn (by intro x hx y hy hxy; exact hinj hx hy hxy)
  have hsum : ∑ x ∈ T, x = ∑ t ∈ S, p t :=
    Finset.sum_image (by intro x hx y hy hxy; exact hinj hx hy hxy)
  have hge : ∀ x ∈ T, (1:ℤ) ≤ x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact h1 t ht
  have key := Finset.sum_range_le_sum (s := T) (c := 1) hge
  have hrange : 2 * ∑ n ∈ Finset.range T.card, ((1:ℤ) + n)
      = (T.card : ℤ) * (T.card + 1) := by
    induction T.card with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        push_cast
        ring
  have : (T.card : ℤ) * (T.card + 1) ≤ 2 * ∑ x ∈ T, x := by
    rw [← hrange]; linarith [key]
  rwa [hcard, hsum] at this
