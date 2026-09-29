-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperR9SourceCounts
-- name    : ErdosProblems_Erdos269_PaperR9SourceCounts
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:14:04.265371+00:00
-- url     : https://prove2.me/theorems/919f74a1-2a8a-4887-82fd-dca62ba1c06d
-- title:
--   PaperR9SourceCounts
-- statement:
--   Defines exact finite algorithms for counting smooth exponent pairs and pure-power prefixes, including floor-sum, division-loop, and sweep forms, and the assembled exact ordered-digit checker.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR9SourceCounts.lean#L1-L348
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact source-count normalisation for certificate reconstruction

This module does not certify a generated list by fiat. It starts with the
library's actual strictSmoothPairs / strictSmoothExponents and proves the
one-dimensional pair count, cumulative pure-power count, threshold difference,
and complete ordered dyadic digit formula.

The executable pair evaluator uses successive division. It does not enumerate
a box of side `x` or compute real logarithms. Its boundary sweep is linear in the two exponent bounds. No unproved
logarithmic-interval or Euclidean floor-sum optimisation is used by this return.

Source APIs reused: RestrictedFloorSum.lean, strictSmoothShell_card,
restrictedPurePowerCount_eq_restrictedLogFloorSum, restrictedLogFloorSum_succ_sub;
Mathlib/Data/Nat/Log.lean; Lean src/Init/Data/Nat/Div/Basic.lean.
Finset.card_eq_sum_card_fiberwise is reused exactly as in the supplied
RestrictedFloorSum.lean:332.

-/
namespace ErdosProblems.Erdos269.PaperR9
open Finset



/-- Strict cutoffs are handled by `x-1`, so this formula also handles exact
prime-power coincidences correctly. No independence hypothesis is needed. -/
def pairCountFast (q r x : ℕ) : ℕ :=
  if x ≤ 1 then 0 else
    ∑ i ∈ range (Nat.log q (x - 1) + 1),
      (Nat.log r ((x - 1) / q ^ i) + 1)



/-- No repeated computation of `q^i`: each step divides the previous quotient. -/
def pairCountDivLoop (q r : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, N =>
    if N = 0 then 0 else Nat.log r N + 1 + pairCountDivLoop q r k (N / q)



/-- Executable count of the ACTUAL strict pair set. -/
def pairCountExact (q r x : ℕ) : ℕ :=
  if x ≤ 1 then 0 else
    pairCountDivLoop q r (Nat.log q (x - 1) + 1) (x - 1)



/-- Decrease a certified upper power until it is the largest power below N.
The power is updated by exact division, rather than re-exponentiation. -/
def lowerPower (r : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, P, _ => (0, P)
  | j + 1, P, N =>
    if P ≤ N then (j + 1, P) else lowerPower r j (P / r) N



/-- Boundary sweep. On a correct state, both the q- and r-power exponents
only decrease, so no inner logarithm is recomputed. -/
def pairCountSweep (q r : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | k + 1, N, j, P =>
    if N = 0 then 0 else
      let jp := lowerPower r j P N
      jp.1 + 1 + pairCountSweep q r k (N / q) jp.1 jp.2



def pairCountChecked (q r x : ℕ) : ℕ :=
  if x ≤ 1 then 0 else
    let N := x - 1
    let j := Nat.log r N
    pairCountSweep q r (Nat.log q N + 1) N j (r ^ j)



/-- This orientation of the cumulative count matches the integer generator. -/
def purePrefixCount (p q r e : ℕ) : ℕ :=
  ∑ k ∈ range e, pairCountChecked q r (p ^ (k + 1))







def orderedDigitExact (a : ℕ) : ℕ :=
  let f3 := Nat.log 3 (2 ^ (a + 1))
  let f5 := Nat.log 5 (2 ^ (a + 1))
  let c2 := purePrefixCount 2 3 5 a
  let d3 := purePrefixCount 3 2 5 f3 - c2
  let d5 := purePrefixCount 5 2 3 f5 - c2
  let w := pairCountChecked 3 5 (2 ^ (a + 1))
  if 3 ^ f3 ≤ 5 ^ f5 then w + 10 * d3 + 4 * d5 else w + 2 * d3 + 12 * d5



end ErdosProblems.Erdos269.PaperR9


