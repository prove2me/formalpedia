-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_sub_one_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:16.81236+00:00
-- url     : https://prove2.me/submissions/04de67b6-1a84-4f27-8265-d23703634d74

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite analytic lemmas for densification

This file isolates the elementary projected-majorant estimates used in one
step of Conlon--Fox--Zhao densification.  It does not state a relative
counting theorem.

If a nonnegative finite majorant `ν` has first and second normalized moments
within `η` of one, then

```
mean (fun x => |ν x - 1|) ≤ √(3 * η).
```

For `0 ≤ g ≤ ν`, truncating `g` pointwise at one produces a `[0,1]`-valued
function.  Its `L¹` loss, and its loss in any pairing against a unit-bounded
factor, are bounded first by the mean excess `max (ν - 1) 0`, and hence by
the same square-root moment bound.  The final section records pointwise and
averaged product-perturbation inequalities used to package the remaining
bounded factors in a densification step.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Projected-majorant moments -/

open Wikipedia.SzemeredisTheorem in
/-- Exact expansion of a centered second moment.  Nonemptiness is the
precise hypothesis needed for the normalized mean of the constant function
one to equal one. -/
theorem solution
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    mean (fun x => (f x - 1) ^ 2) =
      mean (fun x => f x ^ 2) - 2 * mean f + 1 := by
  calc
    mean (fun x => (f x - 1) ^ 2) =
        mean (fun x =>
          f x ^ 2 + ((-2 : ℝ) * f x + 1)) := by
      apply congrArg mean
      funext x
      ring
    _ = mean (fun x => f x ^ 2) +
        mean (fun x => (-2 : ℝ) * f x + 1) :=
      mean_add _ _
    _ = mean (fun x => f x ^ 2) +
        (mean (fun x => (-2 : ℝ) * f x) +
          mean (fun _ : Ω => (1 : ℝ))) := by
      rw [mean_add]
    _ = mean (fun x => f x ^ 2) - 2 * mean f + 1 := by
      rw [mean_smul, mean_const]
      ring
