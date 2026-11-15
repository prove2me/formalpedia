-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_sub_one_sq_eq
-- name    : Wikipedia.SzemeredisTheorem.mean_sub_one_sq_eq
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:57.169256+00:00
-- url     : https://prove2.me/theorems/9597fc8a-c7b3-480b-bedd-c3be27bfd2c3
-- title:
--   Expansion of a centered second moment
-- statement:
--   Let $\Omega$ be nonempty and finite, and let $f:\Omega\to\mathbb R$. Then
--   $$
--   \mathbb E_x(f(x)-1)^2=\mathbb E_x f(x)^2-2\mathbb E_xf(x)+1.
--   $$
--   There are no bounds or sign conditions on $f$. Nonemptiness supplies normalized mean one for the constant function one.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/Densification.lean#L46-L70

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

theorem Wikipedia.SzemeredisTheorem.mean_sub_one_sq_eq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    mean (fun x => (f x - 1) ^ 2) =
      mean (fun x => f x ^ 2) - 2 * mean f + 1 := by sorry
