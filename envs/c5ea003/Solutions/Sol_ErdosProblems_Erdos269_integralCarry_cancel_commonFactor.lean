-- Prove2me | solution 1 for ErdosProblems.Erdos269.integralCarry_cancel_commonFactor
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:58:38.514259+00:00
-- url     : https://prove2.me/submissions/8f457871-02ee-4d0e-9c9e-e1bb968d7e8d

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
# Erdős #269: restricted floor sums and local windows

Problem-owned landing surface for the exact true-shell floor sums and the
local-window residue reduction.  No declaration here asserts the open
cofinal anti-concentration theorem.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators

/-! ## Exact finite strict counts -/

















/-! ## Exact two-dimensional fiber formula -/







































/-! ## Generic logarithmic-window algebra -/



















/-! ## Exact denominator-factor cancellation -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (c d b m : ℕ → ℤ) (smoothFactor reducedDenominator : ℤ)
    (hsmooth : smoothFactor ≠ 0)
    (hfactor : ∀ n, c n = smoothFactor * d n)
    (hrec : ∀ n,
      c (n + 1) = b n * c n -
        (smoothFactor * reducedDenominator) * m n) :
    ∀ n, d (n + 1) = b n * d n - reducedDenominator * m n := by
  intro n
  apply mul_left_cancel₀ hsmooth
  calc
    smoothFactor * d (n + 1) = c (n + 1) := (hfactor (n + 1)).symm
    _ = b n * c n - (smoothFactor * reducedDenominator) * m n := hrec n
    _ = smoothFactor * (b n * d n - reducedDenominator * m n) := by
      rw [hfactor n]
      ring
