-- Prove2me | solution 1 for ResidueDial.realized_speedup_le_avgSpeedup
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:57:41.348725+00:00
-- url     : https://prove2.me/submissions/95cfa2e0-614c-439a-b330-bdd56f75f732

-- Sol generated from Cryptography/ResidueDial/Accounting.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Accounting
import Definitions.Def_Cryptography_ResidueDial_Core
import Theorems.Thm_ResidueDial_schedule_sum_lower_bound

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


theorem avgSpeedup_denom_pos {k j : ℕ} (h : 0 < k + j) :
    0 < (k : ℝ) * (k + 1) + (j : ℝ) * (j + 1) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have hj : 0 < j := by omega
    have : (0:ℝ) < j := by exact_mod_cast hj
    have hk0 : (k:ℝ) = 0 := by exact_mod_cast hk
    rw [hk0]; nlinarith
  · have : (0:ℝ) < k := by exact_mod_cast hk
    have hj : (0:ℝ) ≤ j := by positivity
    nlinarith





/-! ## The accounting gap -/



open ResidueDial in
theorem solution(K : Finset α) (posIn posOut : α → ℤ)
    (hInjIn : Set.InjOn posIn K) (hIn1 : ∀ t ∈ K, 1 ≤ posIn t)
    (hInjOut : Set.InjOn posOut ((univ : Finset α) \ K))
    (hOut1 : ∀ t ∈ (univ : Finset α) \ K, 1 ≤ posOut t)
    (hn : 0 < Fintype.card α) :
    ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) + 1))
        / (2 * (scheduleTotal K posIn posOut : ℝ))
      ≤ avgSpeedup K.card (((univ : Finset α) \ K).card) := by
  classical
  set k := K.card with hk
  set j := ((univ : Finset α) \ K).card with hj
  have hkj : k + j = Fintype.card α := by
    rw [hk, hj, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have : K.card ≤ Fintype.card α := by
      simpa [Finset.card_univ] using Finset.card_le_univ K
    omega
  have hkjR : (k : ℝ) + j = (Fintype.card α : ℝ) := by exact_mod_cast hkj
  have hbound := schedule_sum_lower_bound K posIn posOut hInjIn hIn1 hInjOut hOut1
  have hboundR : (k : ℝ) * (k + 1) + (j : ℝ) * (j + 1)
      ≤ 2 * (scheduleTotal K posIn posOut : ℝ) := by
    exact_mod_cast hbound
  have hDpos : 0 < (k : ℝ) * (k + 1) + (j : ℝ) * (j + 1) :=
    avgSpeedup_denom_pos (by omega)
  have hnum : 0 ≤ (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) + 1) := by positivity
  rw [avgSpeedup, hkjR]
  exact div_le_div_of_nonneg_left hnum hDpos hboundR
