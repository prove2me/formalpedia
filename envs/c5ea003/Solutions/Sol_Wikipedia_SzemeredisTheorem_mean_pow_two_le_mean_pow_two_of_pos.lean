-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_pow_two_le_mean_pow_two_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:54.462551+00:00
-- url     : https://prove2.me/submissions/d0e7ed46-d050-4afe-b9e1-fe53f768de18

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_pow_two_le_mean_pow_two

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- Jensen for an arbitrary real-valued function and a positive power-of-two
exponent.  Positivity of the exponent makes it even, so absolute values can
be inserted before applying the nonnegative version. -/
theorem solution
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {n : ℕ} (hn : 0 < n) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  have heven : Even (2 ^ n) :=
    even_two.pow_of_ne_zero (Nat.ne_of_gt hn)
  have habs :
      |mean f| ≤ mean (fun x => |f x|) := by
    exact Finset.abs_expect_le Finset.univ f
  calc
    mean f ^ (2 ^ n) = |mean f| ^ (2 ^ n) :=
      (heven.pow_abs (mean f)).symm
    _ ≤ mean (fun x => |f x|) ^ (2 ^ n) :=
      pow_le_pow_left₀ (abs_nonneg _) habs _
    _ ≤ mean (fun x => |f x| ^ (2 ^ n)) :=
      mean_pow_two_le_mean_pow_two
        (fun x => |f x|) (fun x => abs_nonneg (f x)) n
    _ = mean (fun x => f x ^ (2 ^ n)) := by
      apply congrArg mean
      funext x
      exact heven.pow_abs (f x)
