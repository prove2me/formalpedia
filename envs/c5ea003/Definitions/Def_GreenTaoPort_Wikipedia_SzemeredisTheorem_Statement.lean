-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:45.833934+00:00
-- url     : https://prove2.me/theorems/9234c212-4af2-4308-b488-204c063115e4
-- title:
--   Sets containing arbitrarily long arithmetic progressions
-- statement:
--   For a set $A\subseteq\mathbb N$, the predicate says that $A$ contains an arithmetic progression of every finite length:
--
--   $$
--   \forall k\in\mathbb N\;\exists a,d\in\mathbb N,\quad d\ge1
--   \quad\text{and}\quad a+jd\in A\ \text{for every }0\le j<k.
--   $$
--
--   Here $a$ is the first term, $d$ is the common difference, $k$ is the requested length, and $j$ is the position in the progression. The positive difference excludes constant progressions. The case $k=0$ is allowed and has an empty membership condition. Applied to the set of natural primes, this is the arithmetic-progression property asserted by the Green–Tao theorem.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Statement.lean#L15-L17

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# The Lean Eval statement of Szemerédi's theorem

This module records the definitions used by the Lean theorem-proving
evaluation.  Keeping them in a small module makes the public theorem's type
easy to compare verbatim with the challenge statement.
-/

namespace SzemeredisTheorem

open scoped BigOperators

/-- A set contains arithmetic progressions of every finite length. -/
def ContainsArbitraryAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A



end SzemeredisTheorem


