-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_pow_two_le_mean_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:57.589829+00:00
-- url     : https://prove2.me/submissions/3eec224e-9996-46f2-b9ae-92a853530b21

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem







/-- Jensen/Cauchy--Schwarz for the square of a normalized finite mean. -/
theorem mean_square_le_mean_square
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    mean f ^ 2 ≤ mean (fun x => f x ^ 2) := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      Finset.univ f (fun _ : Ω => (1 : ℝ))
  simpa [mean] using h









end Wikipedia.SzemeredisTheorem

end
/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- Jensen for powers whose exponent is a power of two, in the form used
after iterating Cauchy--Schwarz. -/
theorem solution
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hmean0 : 0 ≤ mean f := mean_nonneg hf
      have hright0 :
          0 ≤ mean (fun x => f x ^ (2 ^ n)) :=
        mean_nonneg fun x => pow_nonneg (hf x) _
      have hsquare :
          (mean f ^ (2 ^ n)) ^ 2 ≤
            mean (fun x => f x ^ (2 ^ n)) ^ 2 := by
        simpa [pow_two] using
          mul_self_le_mul_self
            (pow_nonneg hmean0 _) ih
      calc
        mean f ^ (2 ^ (n + 1)) =
            (mean f ^ (2 ^ n)) ^ 2 := by
          rw [show 2 ^ (n + 1) = 2 ^ n * 2 by
            rw [pow_succ], pow_mul]
        _ ≤ mean (fun x => f x ^ (2 ^ n)) ^ 2 :=
          hsquare
        _ ≤ mean (fun x =>
            (f x ^ (2 ^ n)) ^ 2) :=
          mean_square_le_mean_square _
        _ = mean (fun x => f x ^ (2 ^ (n + 1))) := by
          apply congrArg mean
          funext x
          rw [show 2 ^ (n + 1) = 2 ^ n * 2 by
            rw [pow_succ], pow_mul]
