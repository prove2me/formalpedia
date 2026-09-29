-- Prove2me | solution 1 for BatchCost.flatSaving_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:58:16.492994+00:00
-- url     : https://prove2.me/submissions/0b250dff-3da5-4db9-ba14-e983c953b6cc

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




/-- Explicit form of the relative saving: a ceiling `(s - c)/s` minus an
amortized setup term `A/(s·k)`. -/
theorem flatSaving_eq (hs : 0 < s) {k : ℚ} (hk : 0 < k) :
    flatSaving A c s k = (s - c) / s - A / (s * k) := by
  unfold flatSaving batchFlat soloFlat
  field_simp
  ring






/-! ## Word model: the sign reverses -/




variable (q c₁ s₁ : ℚ)







/-! ## The E1 / Amdahl cap on a testing-phase improvement -/


variable (F S S' : ℚ)





/-! ## Exp 561 numbers -/







open BatchCost in
theorem solution(hs : 0 < s) :
    Filter.Tendsto (fun n : ℕ => flatSaving A c s (n + 1)) Filter.atTop
      (nhds ((s - c) / s)) := by
  have hEq : ∀ n : ℕ, flatSaving A c s (n + 1)
      = (s - c) / s - A / s * (1 / ((n : ℚ) + 1)) := by
    intro n
    have hk : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    rw [flatSaving_eq A c s hs hk]
    field_simp
  simp only [hEq]
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℚ) + 1)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n : ℕ => ((n : ℚ) + 1)) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    simpa using this.inv_tendsto_atTop
  have := (h0.const_mul (A / s))
  simpa using (Filter.Tendsto.const_sub ((s - c) / s) this)
