-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_hasFiniteDenseModel_of_positivePartCorrelationBound
-- name    : Wikipedia.SzemeredisTheorem.hasFiniteDenseModel_of_positivePartCorrelationBound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:09:17.886571+00:00
-- url     : https://prove2.me/theorems/47d41c10-c0da-4cfd-99e4-db2a801e2ae6
-- title:
--   A one-sided positive-part correlation bound gives a finite dense model
-- statement:
--   Let $\Omega,\tau$ be finite, let $q$ be any real test family, and let $0\le f\le\nu$ with $\varepsilon\ge0$. Suppose every coefficient vector $c$ has pairing of $\nu-1$ with the positive part of its test combination at most $\varepsilon\|c\|_1$. Then $f$ has a unit-bounded finite dense model against $q$ with error $\varepsilon$. The pseudorandomness hypothesis is one-sided.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L752-L782

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/
open Wikipedia.SzemeredisTheorem
open scoped Pointwise

theorem Wikipedia.SzemeredisTheorem.hasFiniteDenseModel_of_positivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) {f ν : Ω → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hpseudo : HasPositivePartCorrelationBound q ν ε) :
    HasFiniteDenseModel q f ε := by sorry
