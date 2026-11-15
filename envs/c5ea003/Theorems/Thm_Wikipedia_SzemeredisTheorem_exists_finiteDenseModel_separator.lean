-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_finiteDenseModel_separator
-- name    : Wikipedia.SzemeredisTheorem.exists_finiteDenseModel_separator
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:55:41.870813+00:00
-- url     : https://prove2.me/theorems/2c12b61c-28f5-4212-980d-cf209f202861
-- title:
--   Failure of a finite dense model gives a strict linear separator
-- statement:
--   Let $\Omega,\tau$ be finite types, let $q$ be a real test family and $f$ a real function, and let $\varepsilon\ge0$. If the finite dense-model problem fails, there is a nonzero continuous real linear functional on the profile space which strictly separates the target profile of $f$ from every unit-bounded model profile plus every admissible error vector in the profile-error set.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L328-L369

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

theorem Wikipedia.SzemeredisTheorem.exists_finiteDenseModel_separator
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (f : Ω → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : ¬HasFiniteDenseModel q f ε) :
    ∃ L : StrongDual ℝ (τ → ℝ), L ≠ 0 ∧
      ∀ (g : Ω → ℝ), IsUnitBounded g →
        ∀ e ∈ profileErrorSet τ ε,
          L (finiteTestProfile q g + e) <
            L (finiteTestProfile q f) := by sorry
