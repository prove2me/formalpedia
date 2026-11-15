-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_hasFiniteDenseModel_iff_profile_mem
-- name    : Wikipedia.SzemeredisTheorem.hasFiniteDenseModel_iff_profile_mem
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:37.434202+00:00
-- url     : https://prove2.me/theorems/9686b4b8-98f1-4cba-a8ba-102ea16be277
-- title:
--   Finite dense-model feasibility is profile-set membership
-- statement:
--   For finite types $\Omega,\tau$, a real test family $q$, real function $f$, and real error $\varepsilon$, a finite dense model exists exactly when the target test profile of $f$ belongs to the enlarged dense-model profile set with error $\varepsilon$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L290-L326

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

theorem Wikipedia.SzemeredisTheorem.hasFiniteDenseModel_iff_profile_mem
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (ε : ℝ) :
    HasFiniteDenseModel q f ε ↔
      finiteTestProfile q f ∈
        denseModelProfileSet Ω τ q ε := by sorry
