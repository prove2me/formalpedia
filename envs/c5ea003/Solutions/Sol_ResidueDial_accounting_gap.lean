-- Prove2me | solution 1 for ResidueDial.accounting_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:44:28.323893+00:00
-- url     : https://prove2.me/submissions/bf208d05-7c03-4813-aa70-7e0240c483ec

-- Sol generated from Cryptography/ResidueDial/Accounting.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Accounting
import Definitions.Def_Cryptography_ResidueDial_Core
import Theorems.Thm_ResidueDial_speedup_le_four_thirds

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

/-- **The `2` barrier of expected-position accounting: strict.**  However the
dial splits the class space, the expected-position speedup is `< 2`. -/
theorem avgSpeedup_lt_two {k j : ℕ} (h : 0 < k + j) : avgSpeedup k j < 2 := by
  have hden := avgSpeedup_denom_pos h
  rw [avgSpeedup, div_lt_iff₀ hden]
  have hk : (0:ℝ) ≤ k := by positivity
  have hj : (0:ℝ) ≤ j := by positivity
  have hpos : (0:ℝ) < (k : ℝ) + j := by
    have : 0 < ((k + j : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  nlinarith [sq_nonneg ((k : ℝ) - j)]

/-- Balanced blocks give the exact value `(2m+1)/(m+1)`. -/
theorem avgSpeedup_balanced {m : ℕ} (hm : 0 < m) :
    avgSpeedup m m = (2 * (m : ℝ) + 1) / ((m : ℝ) + 1) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  rw [avgSpeedup]
  rw [div_eq_div_iff (by nlinarith) (by linarith)]
  ring



/-! ## The accounting gap -/



open ResidueDial in
theorem solution(ε : ℝ) (hε : 0 < ε) :
    (∀ θ : ℝ, speedup θ ≤ 4 / 3) ∧ (4 / 3 : ℝ) < 2 ∧
      ∃ m : ℕ, 0 < m ∧ 2 - ε < avgSpeedup m m ∧ avgSpeedup m m < 2 := by
  refine ⟨speedup_le_four_thirds, by norm_num, ?_⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  refine ⟨m + 1, Nat.succ_pos m, ?_, avgSpeedup_lt_two (by omega)⟩
  have hm1 : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hεm : 1 / ((m : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hm1]
    have h1 : 1 / ε < (m : ℝ) := hm
    rw [div_lt_iff₀ hε] at h1
    nlinarith
  rw [avgSpeedup_balanced (Nat.succ_pos m)]
  push_cast
  have hval : (2 * ((m : ℝ) + 1) + 1) / (((m : ℝ) + 1) + 1) = 2 - 1 / ((m : ℝ) + 2) := by
    have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  rw [hval]
  have : 1 / ((m : ℝ) + 2) < ε := lt_of_le_of_lt (by
    apply one_div_le_one_div_of_le hm1; linarith) hεm
  linarith
