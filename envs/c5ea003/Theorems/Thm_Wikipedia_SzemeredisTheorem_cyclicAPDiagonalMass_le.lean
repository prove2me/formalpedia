-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPDiagonalMass_le
-- name    : Wikipedia.SzemeredisTheorem.cyclicAPDiagonalMass_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:37.19857+00:00
-- url     : https://prove2.me/theorems/b536dc59-fe62-4c26-8126-049f0e14876a
-- title:
--   Bounding the diagonal progression mass by weight height and mean
-- statement:
--   For a positive modulus $N$, length $k\ge1$, and a real cyclic weight with $0\le f\le B$, the diagonal mass satisfies
--
--   $$
--   \sum_{a\in\mathbb Z/N\mathbb Z}f(a)^k
--   \le B^{k-1}N\,\mathbb E f.
--   $$
--
--   The diagonal consists of the constant progressions with common difference zero.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/CountExtraction.lean#L59-L80

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

theorem Wikipedia.SzemeredisTheorem.cyclicAPDiagonalMass_le
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B) :
    cyclicAPDiagonalMass k N f ≤
      B ^ (k - 1) * (N : ℝ) * mean f := by sorry
