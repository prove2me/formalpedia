-- Prove2me | solution 1 for ErdosProblems.Erdos269.integralCarry_window
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:58:39.186648+00:00
-- url     : https://prove2.me/submissions/74fef45d-7cf1-40d2-af0a-0cf4413351c7

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









/-- Any first-order affine recurrence unrolls exactly into the local base and
local forcing.  This is the algebraic heart of the logarithmic-window
compression and is independent of the still-open floor-sum anti-concentration
producer. -/
theorem affineRecurrence_window
    (A b e : ℕ → ℤ) (lo len : ℕ)
    (hrec : ∀ n, A (n + 1) = b n * A n + e n) :
    A (lo + len) =
      windowBase b lo len * A lo + windowForcing b e lo len := by
  induction len with
  | zero => simp [windowBase, windowForcing]
  | succ len ih =>
      rw [Nat.add_succ, hrec, ih]
      simp only [windowBase, windowForcing]
      ring

/-- Scaling every forcing term scales the accumulated local numerator by the
same constant. -/
theorem windowForcing_const_mul
    (b e : ℕ → ℤ) (B : ℤ) (lo len : ℕ) :
    windowForcing b (fun n => B * e n) lo len =
      B * windowForcing b e lo len := by
  induction len with
  | zero => simp [windowForcing]
  | succ len ih =>
      simp only [windowForcing, ih]
      ring
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (c b m : ℕ → ℤ) (B : ℤ) (lo len : ℕ)
    (hrec : ∀ n, c (n + 1) = b n * c n - B * m n) :
    c (lo + len) =
      windowBase b lo len * c lo -
        B * windowForcing b m lo len := by
  have hrec' : ∀ n, c (n + 1) = b n * c n + (-B) * m n := by
    intro n
    rw [hrec]
    ring
  rw [affineRecurrence_window c b (fun n => (-B) * m n) lo len hrec']
  rw [windowForcing_const_mul b m (-B) lo len]
  ring
