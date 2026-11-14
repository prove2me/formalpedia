-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
-- name    : GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:33.353337+00:00
-- url     : https://prove2.me/theorems/47700222-931d-488b-843b-f61548bb4c40
-- title:
--   Finite arithmetic progressions in a set
-- statement:
--   Let $A\subseteq\mathbb N$ and let $k,a,d\in\mathbb N$. The predicate for a progression in $A$ requires
--
--   $$
--   d>0\quad\text{and}\quad a+dj\in A\quad\text{for every }j<k.
--   $$
--
--   Here $a$ is the initial term, $d$ is the common difference, and $k$ is the length. A second predicate asserts the existence of such $a$ and $d$ for the specified length. No positivity condition is imposed on $a$. For $k=0$, the membership condition is empty, while the step is still required to be positive.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/ArithmeticProgression/Basic.lean#L5-L13

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace Wikipedia.SzemeredisTheorem

/-- `IsAPIn A k a d` says that the first `k` terms of the natural-number
arithmetic progression with initial term `a` and positive step `d` lie in
`A`. -/
def IsAPIn (A : Set ℕ) (k a d : ℕ) : Prop :=
  0 < d ∧ ∀ j : ℕ, j < k → a + d * j ∈ A

/-- A set contains an arithmetic progression of the specified length. -/
def ContainsAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, IsAPIn A k a d

































end Wikipedia.SzemeredisTheorem


