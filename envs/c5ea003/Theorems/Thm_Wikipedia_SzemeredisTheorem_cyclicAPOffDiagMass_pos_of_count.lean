-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPOffDiagMass_pos_of_count
-- name    : Wikipedia.SzemeredisTheorem.cyclicAPOffDiagMass_pos_of_count
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:55.017199+00:00
-- url     : https://prove2.me/theorems/c95772b6-ca76-4eeb-b3d6-38b3433201c6
-- title:
--   A count exceeding the diagonal bound has positive off-diagonal mass
-- statement:
--   Let $N>0$, $k\ge1$, and $0\le f\le B$ on $\mathbb Z/N\mathbb Z$. If
--
--   $$
--   B^{k-1}\mathbb E f<N\,\operatorname{APCount}_k(f),
--   $$
--
--   then the unnormalized $k$-term progression mass with nonzero common difference is strictly positive.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/CountExtraction.lean#L158-L182

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

theorem Wikipedia.SzemeredisTheorem.cyclicAPOffDiagMass_pos_of_count
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B)
    (hcount :
      B ^ (k - 1) * mean f <
        (N : ℝ) * cyclicAPCount k N f) :
    0 < cyclicAPOffDiagMass k N f := by sorry
