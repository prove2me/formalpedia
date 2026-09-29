-- Prove2me | Definitions.Def_Applications_BatchSmoothnessCost
-- name    : Applications_BatchSmoothnessCost
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:32:10.509799+00:00
-- url     : https://prove2.me/theorems/b88212fc-cd2d-4a30-a22c-67190f1771c6
-- title:
--   Aether Catalog definitions — Applications_BatchSmoothnessCost
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.BatchSmoothnessCost`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/BatchSmoothnessCost.lean by skeleton subtraction
import Mathlib

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

namespace BatchCost

/-! ## Product trees: node counts and word counts -/

/-- Number of multiplications in a balanced product tree over `2 ^ L` leaves
(one op per internal node — the *flat* op model). -/
def treeFlatOps : ℕ → ℕ
  | 0 => 0
  | L + 1 => 2 * treeFlatOps L + 1


/-- Word-operation cost of a balanced product tree over `2 ^ L` leaves, each of
`w` machine words, with schoolbook multiplication: the top multiplication
combines two `2 ^ L · w`-word operands at cost `(2 ^ L · w) ^ 2`. -/
def treeWordCost (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 => 2 * treeWordCost w L + (2 ^ L * w) ^ 2



/-! ## Flat op model: batch amortizes, with no crossover -/

section Flat

variable (A c s : ℚ)

/-- Flat-model cost of testing a pool of `k` candidates in batch: a one-off
setup `A` (factor-base product tree) plus `c` per candidate (remainder-tree node
and repeated squarings). -/
def batchFlat (k : ℚ) : ℚ := A + c * k

/-- Flat-model cost of solo trial division: `s` operations per candidate. -/
def soloFlat (k : ℚ) : ℚ := s * k

/-- Relative saving of batch over solo on a pool of `k` candidates. -/
noncomputable def flatSaving (k : ℚ) : ℚ := 1 - batchFlat A c k / soloFlat s k






end Flat

/-! ## Word model: the sign reverses -/



section Word

variable (q c₁ s₁ : ℚ)

/-- Continuous two-parameter word model: batch pays a quadratic big-integer term
`q·k(k-1)` (product and remainder trees) plus `c₁` per candidate. -/
def batchWord (k : ℚ) : ℚ := q * k * (k - 1) + c₁ * k

/-- Solo word cost stays linear. -/
def soloWord (k : ℚ) : ℚ := s₁ * k




end Word

/-! ## The E1 / Amdahl cap on a testing-phase improvement -/

section Amdahl

variable (F S S' : ℚ)




end Amdahl

/-! ## Exp 561 numbers -/

/-- Measured testing share of per-factor work. -/
def e1Share : ℚ := 1156 / 10000

/-- Measured overall improvement of the batch arm. -/
def measuredDelta : ℚ := 104 / 1000




end BatchCost


