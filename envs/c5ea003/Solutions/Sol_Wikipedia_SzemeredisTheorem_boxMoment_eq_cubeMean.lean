-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.boxMoment_eq_cubeMean
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:44.308809+00:00
-- url     : https://prove2.me/submissions/7e05f7d6-1164-40aa-af2e-8d6e39f6674b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cubeProduct_cons
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_fin_cons

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Finite box moments and generalized von Neumann

This file packages the iterated Cauchy--Schwarz argument for a function on a
finite product.  A coordinate cut form pairs the function with one bounded
factor for every deleted coordinate.  Its `2 ^ n`-th power is bounded by the
recursive `n`-dimensional box moment.

The recursive definition duplicates one coordinate at a time.  It is
definitionally aligned with the Cauchy--Schwarz proof and is equivalent to
the usual average of the product over all vertices of an `n`-cube.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators















@[simp]
theorem boxMoment_zero {G : Type*} [Fintype G]
    (F : (Fin 0 → G) → ℝ) :
    boxMoment 0 F = mean F :=
  rfl

@[simp]
theorem boxMoment_succ {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    boxMoment (n + 1) F =
      mean fun p : G × G =>
        boxMoment n (pairedTupleFunction F p) :=
  rfl















/-- The explicit cube mean obeys the same successor recursion as
`boxMoment`. -/
theorem cubeMean_succ
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    cubeMean (n + 1) F =
      mean fun p : G × G =>
        cubeMean n (pairedTupleFunction F p) := by
  unfold cubeMean
  rw [mean_fin_cons]
  unfold mean₂
  apply congrArg mean
  funext p
  apply congrArg mean
  funext x
  exact cubeProduct_cons F p x



































end Wikipedia.SzemeredisTheorem

end
/-!
# Finite box moments and generalized von Neumann

This file packages the iterated Cauchy--Schwarz argument for a function on a
finite product.  A coordinate cut form pairs the function with one bounded
factor for every deleted coordinate.  Its `2 ^ n`-th power is bounded by the
recursive `n`-dimensional box moment.

The recursive definition duplicates one coordinate at a time.  It is
definitionally aligned with the Cauchy--Schwarz proof and is equivalent to
the usual average of the product over all vertices of an `n`-cube.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Recursive and explicit cube-vertex descriptions of the box moment
coincide. -/
theorem solution
    {G : Type*} [Fintype G] :
    ∀ (n : ℕ) (F : (Fin n → G) → ℝ),
      boxMoment n F = cubeMean n F := by
  intro n
  induction n with
  | zero =>
      intro F
      rw [boxMoment_zero]
      unfold cubeMean mean
      apply Fintype.expect_equiv (Equiv.ofUnique _ _)
      intro x
      rw [Fintype.prod_unique]
      exact congrArg F (Subsingleton.elim _ _)
  | succ n ih =>
      intro F
      rw [boxMoment_succ, cubeMean_succ]
      apply congrArg mean
      funext p
      exact ih (pairedTupleFunction F p)
