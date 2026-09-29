-- Prove2me | Definitions.Def_Logic_RepairedAntiFibonacciClassification
-- name    : Logic_RepairedAntiFibonacciClassification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:22.637869+00:00
-- url     : https://prove2.me/theorems/a6f53c32-9c19-4ac4-9bfe-400028fe2645
-- title:
--   Aether Catalog definitions — Logic_RepairedAntiFibonacciClassification
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.RepairedAntiFibonacciClassification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/RepairedAntiFibonacciClassification.lean by skeleton subtraction
import Mathlib

/-!
# Classification of the repaired anti-Fibonacci process

The global additive repair from `Novelty.RepairedAntiFibonacci` is not merely
well-defined and increasing: its trajectory is forced exactly.  Starting from
one, the greedy process enumerates the positive odd integers.

The key point is that sums of earlier odd values are even.  At stage `n`, the
next odd value `2n+3` is therefore admissible, while the only smaller candidate
above `2n+1`, namely `2n+2`, is already the sum of the first and current values.
This gives both existence and uniqueness, and turns the earlier exponential
one-step ceiling into an exact linear law.
-/

namespace RepairedAntiFibonacci

noncomputable section

/-- Pair sums formed from values whose indices are strictly below `n`. -/
def priorPairSums (a : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  ((Finset.range n) ×ˢ (Finset.range n)).image fun ij => a ij.1 + a ij.2

/-- A candidate exceeds the current value and avoids every prior pair sum. -/
def AdmissibleAfter (a : ℕ → ℕ) (n z : ℕ) : Prop :=
  a n < z ∧ z ∉ priorPairSums a (n + 1)

/-- `z` is the least admissible successor after time `n`. -/
def IsGreedySuccessor (a : ℕ → ℕ) (n z : ℕ) : Prop :=
  AdmissibleAfter a n z ∧ ∀ w, AdmissibleAfter a n w → z ≤ w

/-- A repaired trajectory begins at one and always takes the least globally
additively admissible successor. -/
def SatisfiesRepairedRule (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n, IsGreedySuccessor a n (a (n + 1))


/-- The unique candidate trajectory: the positive odd integers. -/
def canonical (n : ℕ) : ℕ := 2 * n + 1
















end

end RepairedAntiFibonacci


