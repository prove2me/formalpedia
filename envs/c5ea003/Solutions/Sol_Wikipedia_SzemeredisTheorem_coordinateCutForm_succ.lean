-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.coordinateCutForm_succ
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:07:40.816237+00:00
-- url     : https://prove2.me/submissions/67080ef8-44b6-4fe0-9c85-355db1771648

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_fin_cons

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
theorem eraseCoordinate_zero_cons
    {G : Type*} {n : ℕ} (a : G) (y : Fin n → G) :
    eraseCoordinate (0 : Fin (n + 1)) (Fin.cons a y) = y := by
  funext j
  simp [eraseCoordinate_apply]

























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
/-- Split a successor-dimensional cut form into the deleted-head factor and
the remaining inner integrand. -/
theorem solution
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1)) :
    coordinateCutForm (n + 1) F u =
      mean₂ fun y : Fin n → G => fun a : G =>
        u 0 y * tailCutIntegrand F u y a := by
  calc
    coordinateCutForm (n + 1) F u =
        mean₂ (fun a : G => fun y : Fin n → G =>
          F (Fin.cons a y) *
            ∏ i, u i
              (eraseCoordinate i (Fin.cons a y))) := by
      exact mean_fin_cons _
    _ = mean₂ (fun y : Fin n → G => fun a : G =>
          F (Fin.cons a y) *
            ∏ i, u i
              (eraseCoordinate i (Fin.cons a y))) :=
      mean₂_comm _
    _ = mean₂ fun y : Fin n → G => fun a : G =>
          u 0 y * tailCutIntegrand F u y a := by
      apply congrArg mean
      funext y
      apply congrArg mean
      funext a
      simp only
      rw [Fin.prod_univ_succ]
      simp only [eraseCoordinate_zero_cons]
      simp [tailCutIntegrand]
      ring
