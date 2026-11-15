-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_boxSum_sub_trimmed_le
-- name    : Wikipedia.SzemeredisTheorem.abs_boxSum_sub_trimmed_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:38.593191+00:00
-- url     : https://prove2.me/theorems/fd9811ac-aa94-471f-9550-77b59e424c73
-- title:
--   A boundary bound for differences of box sums
-- statement:
--   For a finite coordinate type with decidable equality, natural side lengths, and any natural trimming modulus $D$, suppose $|F(x)|\le B$ on the original box. The difference between its original and trimmed box sums has absolute value at most $B$ times the cardinality of the removed boundary.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CongruenceAverage.lean#L436-L455

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Congruence averages on finite boxes

This file supplies the elementary finite-arithmetic layer used after expanding
the Selberg sieve weight.  A finite family of divisor moduli is combined by an
LCM, while a function depending only on coordinatewise residues is averaged
exactly over boxes whose side lengths are multiples of that LCM.

There are two equivalent box models:

* `natBox side` is the literal finset of natural-valued points satisfying
  `x i < side i`;
* `FiniteBox side` is the finite type `∀ i, Fin (side i)`.

The second model makes quotient--remainder reindexing transparent, and
`boxSum_eq_sum_natBox` transports its sums back to the literal finset.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## LCM bounds -/
/-! ## Finite boxes -/
/-! ## Coordinatewise periodicity and exact box sums -/
/-! ## Exact means -/
/-! ## Trimming and explicit boundary loss -/

theorem Wikipedia.SzemeredisTheorem.abs_boxSum_sub_trimmed_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ) (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hF : ∀ x ∈ natBox side, |F x| ≤ B) :
    |boxSum side F - boxSum (trimmedSide D side) F| ≤
      ((natBox side \ natBox (trimmedSide D side)).card : ℝ) * B := by sorry
