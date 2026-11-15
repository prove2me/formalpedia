-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.coordinateCutForm_pow_le_boxMoment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:05.795194+00:00
-- url     : https://prove2.me/submissions/9dbbbbbb-297b-4469-bca7-374b4f1c9ffd

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_coordinateCutForm_sq_le_paired_mean
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_pow_two_le_mean_pow_two_of_pos

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem













/-- Jensen for every power-of-two exponent.  At exponent one it is an
identity; positive exponents are covered by
`mean_pow_two_le_mean_pow_two_of_pos`. -/
theorem mean_pow_two_le_mean_pow_two'
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (n : ℕ) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  cases n with
  | zero => simp
  | succ n =>
      exact mean_pow_two_le_mean_pow_two_of_pos f (Nat.succ_pos n)



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
theorem boxMoment_zero {G : Type*} [Fintype G]
    (F : (Fin 0 → G) → ℝ) :
    boxMoment 0 F = mean F :=
  rfl

































theorem pairedTailCut_abs_le_one
    {G : Type*} {n : ℕ}
    {u : CutTestFamily G (n + 1)}
    (hu : IsAbsBoundedCutTest u) (p : G × G) :
    IsAbsBoundedCutTest (pairedTailCut u p) := by
  intro i z
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      rw [pairedTailCut, abs_mul]
      exact mul_le_one₀ (hu i.succ _) (abs_nonneg _) (hu i.succ _)



















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
/-- Generalized von Neumann inequality for finite coordinate cut forms.
After one Cauchy--Schwarz step per coordinate, every cut factor has
disappeared and the resulting expression is the full recursive box moment.
-/
theorem solution
    {G : Type*} [Fintype G] [Nonempty G] :
    ∀ (n : ℕ) (F : (Fin n → G) → ℝ)
      (u : CutTestFamily G n),
      IsAbsBoundedCutTest u →
        coordinateCutForm n F u ^ (2 ^ n) ≤
          boxMoment n F := by
  intro n
  induction n with
  | zero =>
      intro F u _
      simp [coordinateCutForm]
  | succ n ih =>
      intro F u hu
      let C : G × G → ℝ := fun p =>
        coordinateCutForm n
          (pairedTupleFunction F p) (pairedTailCut u p)
      have hcs :
          coordinateCutForm (n + 1) F u ^ 2 ≤ mean C := by
        simpa [C] using
          coordinateCutForm_sq_le_paired_mean F u hu
      calc
        coordinateCutForm (n + 1) F u ^ (2 ^ (n + 1)) =
            (coordinateCutForm (n + 1) F u ^ 2) ^ (2 ^ n) := by
          rw [pow_succ, mul_comm, pow_mul]
        _ ≤ mean C ^ (2 ^ n) :=
          pow_le_pow_left₀ (sq_nonneg _) hcs _
        _ ≤ mean (fun p => C p ^ (2 ^ n)) :=
          mean_pow_two_le_mean_pow_two' C n
        _ ≤ mean (fun p : G × G =>
            boxMoment n (pairedTupleFunction F p)) := by
          apply mean_mono
          intro p
          exact ih
            (pairedTupleFunction F p)
            (pairedTailCut u p)
            (pairedTailCut_abs_le_one hu p)
        _ = boxMoment (n + 1) F :=
          rfl
