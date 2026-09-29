-- Prove2me | solution 1 for BatchCost.treeWordCost_closed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:41:49.179652+00:00
-- url     : https://prove2.me/submissions/17c67e38-be30-42ca-b09f-13cbde6dca4c

-- Sol generated from Applications/BatchSmoothnessCost.lean
import Mathlib
import Definitions.Def_Applications_BatchSmoothnessCost

/-!
# Cost models for batch smoothness testing: amortization, reversal, and the Amdahl cap

Companion to `Catalog/Applications/BatchSmoothnessCorrectness.lean`, which shows
that product-tree batch smoothness testing decides exactly the same predicate as
solo trial division.  Here we formalise *what it costs*, reproducing the three
quantitative phenomena measured in exp 561 (`B = 100`, bit length `40`, pools
`k ∈ {1, 8, 64, 512}`):

1. **Flat op model: batch wins at every pool size, and the win grows with `k`.**
   Batch work splits into a one-off setup `A` (building the factor-base product
   tree) plus a per-candidate cost `c`; solo work is `s` per candidate.  The
   relative saving is `(s - c)/s - A/(s·k)`, strictly increasing in `k` and
   converging to the ceiling `(s - c)/s` (`flatSaving_strictMono`,
   `flatSaving_tendsto`).  If `A < s - c` there is *no crossover*: batch is
   cheaper already at `k = 1` (`flat_batch_lt_solo`).

2. **Word model: the sign reverses at large pools.**  With schoolbook
   arithmetic a product tree over `2 ^ L` leaves of `w` words costs
   `w² (4 ^ L - 2 ^ L)/2` word operations (`treeWordCost_closed`), i.e.
   *quadratic* in the pool size, against solo's linear cost.  Hence batch loses
   for every pool beyond an explicit threshold (`word_batch_reversal`), and in
   the two-parameter continuous model the crossover is unique and given in
   closed form (`word_crossover`).  Calibrating the model to the measured
   crossover `M* ≈ 1715` is `word_crossover_calibrated`.

3. **E1 / Amdahl cap.**  Testing is only a fraction `f` of per-factor work
   (measured `f = 11.56 %`), so *no* testing improvement can save more than `f`
   overall (`overall_saving_le_testing_share`), and the end-to-end speedup
   factor is capped by `1/(1 - f)` (`speedup_factor_le`) — a constant, hence
   zero class movement.  Conversely the measured overall `+0.104` pins the
   testing phase down to `29/289 ≈ 10.03 %` of its former cost
   (`exp561_phase_residual`).

All cost quantities are exact (`ℕ` counts, `ℚ` ratios); nothing here is
numerical simulation.
-/

open BatchCost

/-! ## Product trees: node counts and word counts -/






/-! ## Flat op model: batch amortizes, with no crossover -/


variable (A c s : ℚ)










/-! ## Word model: the sign reverses -/




variable (q c₁ s₁ : ℚ)







/-! ## The E1 / Amdahl cap on a testing-phase improvement -/


variable (F S S' : ℚ)





/-! ## Exp 561 numbers -/







open BatchCost in
theorem solution(w L : ℕ) :
    2 * treeWordCost w L + w ^ 2 * 2 ^ L = w ^ 2 * 4 ^ L := by
  induction L with
  | zero => simp [treeWordCost]
  | succ L ih =>
      have h4 : (4 : ℕ) ^ (L + 1) = 4 * 4 ^ L := by ring
      have h2 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
      have hpow : (4 : ℕ) ^ L = 2 ^ L * 2 ^ L := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      have hsq : (2 ^ L * w) ^ 2 = w ^ 2 * 4 ^ L := by
        rw [mul_pow, hpow]; ring
      rw [treeWordCost, h4, h2, hsq]
      nlinarith [ih]
