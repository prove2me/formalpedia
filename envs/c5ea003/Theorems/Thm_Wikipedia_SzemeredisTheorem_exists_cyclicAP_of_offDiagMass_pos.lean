-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cyclicAP_of_offDiagMass_pos
-- name    : Wikipedia.SzemeredisTheorem.exists_cyclicAP_of_offDiagMass_pos
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:55:42.384779+00:00
-- url     : https://prove2.me/theorems/16ba54c9-b699-47f6-83a0-8617ee9b1c84
-- title:
--   Positive off-diagonal mass yields a nonconstant positive cyclic progression
-- statement:
--   Let $N\ne0$ and let $f:\mathbb Z/N\mathbb Z\to\mathbb R$ be nonnegative. If its length-$k$ off-diagonal cyclic AP mass is positive, there are $a,d\in\mathbb Z/N\mathbb Z$ with $d\ne0$ such that $f(a+jd)>0$ for every $j\in\mathrm{Fin}(k)$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/CountExtraction.lean#L203-L230

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

theorem Wikipedia.SzemeredisTheorem.exists_cyclicAP_of_offDiagMass_pos
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hmass : 0 < cyclicAPOffDiagMass k N f) :
    ∃ a d : ZMod N, d ≠ 0 ∧
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by sorry
