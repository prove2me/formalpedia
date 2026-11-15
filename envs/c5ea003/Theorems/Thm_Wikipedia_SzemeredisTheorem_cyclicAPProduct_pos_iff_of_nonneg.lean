-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPProduct_pos_iff_of_nonneg
-- name    : Wikipedia.SzemeredisTheorem.cyclicAPProduct_pos_iff_of_nonneg
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:53:15.679794+00:00
-- url     : https://prove2.me/theorems/929e183e-8aa7-45f3-9f36-3f172214bb77
-- title:
--   A nonnegative progression product is positive exactly when every term is
-- statement:
--   For any natural length and modulus, any nonnegative real cyclic weight $f$, and any cyclic progression $(a+jd)$,
--
--   $$
--   \prod_{j<k}f(a+jd)>0
--   \quad\Longleftrightarrow\quad
--   f(a+jd)>0\text{ for every }j<k.
--   $$
--
--   The statement includes length zero under the empty-product convention and does not require a positive modulus.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/CountExtraction.lean#L184-L201

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.cyclicAPProduct_pos_iff_of_nonneg
    {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 < cyclicAPProduct k N f a d ↔
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by sorry
