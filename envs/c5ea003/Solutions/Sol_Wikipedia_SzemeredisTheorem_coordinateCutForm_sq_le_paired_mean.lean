-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.coordinateCutForm_sq_le_paired_mean
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:08.211995+00:00
-- url     : https://prove2.me/submissions/8b107846-73b9-4c75-a412-6f8827f6e9a4

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cauchySchwarz_eliminate_outer_factor
import Theorems.Thm_Wikipedia_SzemeredisTheorem_coordinateCutForm_succ

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

































theorem mean₂_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean₂ f = mean₂ (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f

end Wikipedia.SzemeredisTheorem

end

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































end Wikipedia.SzemeredisTheorem

end

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
theorem eraseCoordinate_succ_cons
    {G : Type*} {n : ℕ} (i : Fin (n + 1))
    (a : G) (y : Fin (n + 1) → G) :
    eraseCoordinate i.succ (Fin.cons a y) =
      Fin.cons a (eraseCoordinate i y) := by
  funext j
  cases j using Fin.cases with
  | zero =>
      simp [eraseCoordinate_apply]
  | succ j =>
      simp [eraseCoordinate_apply]









/-- Multiplying the two inner integrands produced by Cauchy--Schwarz is
exactly the lower-dimensional cut integrand with paired function and paired
cut factors. -/
theorem tailCutIntegrand_mul
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1))
    (y : Fin n → G) (p : G × G) :
    tailCutIntegrand F u y p.1 *
        tailCutIntegrand F u y p.2 =
      pairedTupleFunction F p y *
        ∏ i, pairedTailCut u p i (eraseCoordinate i y) := by
  cases n with
  | zero =>
      simp [tailCutIntegrand, pairedTupleFunction]
  | succ n =>
      simp only [tailCutIntegrand, pairedTupleFunction]
      rw [mul_mul_mul_comm]
      rw [← Finset.prod_mul_distrib]
      simp only [eraseCoordinate_succ_cons, pairedTailCut]
      rfl













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
/-- One Cauchy--Schwarz step: delete the head cut factor, duplicate the head
coordinate, and pair all remaining factors. -/
theorem solution
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1))
    (hu : IsAbsBoundedCutTest u) :
    coordinateCutForm (n + 1) F u ^ 2 ≤
      mean fun p : G × G =>
        coordinateCutForm n
          (pairedTupleFunction F p) (pairedTailCut u p) := by
  rw [coordinateCutForm_succ]
  calc
    mean₂ (fun y : Fin n → G => fun a : G =>
        u 0 y * tailCutIntegrand F u y a) ^ 2 ≤
        mean₂ (fun y : Fin n → G => fun p : G × G =>
          tailCutIntegrand F u y p.1 *
            tailCutIntegrand F u y p.2) :=
      cauchySchwarz_eliminate_outer_factor
        (fun y : Fin n → G => u 0 y)
        (fun y : Fin n → G => fun a : G =>
          tailCutIntegrand F u y a)
        (fun y => hu 0 y)
    _ = mean₂ (fun p : G × G => fun y : Fin n → G =>
          tailCutIntegrand F u y p.1 *
            tailCutIntegrand F u y p.2) :=
      mean₂_comm _
    _ = mean (fun p : G × G =>
          coordinateCutForm n
            (pairedTupleFunction F p) (pairedTailCut u p)) := by
      unfold mean₂
      apply congrArg mean
      funext p
      unfold coordinateCutForm
      apply congrArg mean
      funext y
      exact tailCutIntegrand_mul F u y p
