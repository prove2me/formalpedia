-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.coefficientL1_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:02:32.616117+00:00
-- url     : https://prove2.me/submissions/7df8e804-9b8b-4b33-8728-b07a0a2a500a

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

open Wikipedia.SzemeredisTheorem in
/-- The coefficient `ℓ¹`-norm vanishes exactly on the zero vector. -/
theorem solution
    {τ : Type*} [Fintype τ] (c : τ → ℝ) :
    coefficientL1 c = 0 ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext t
    have ht : |c t| = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => abs_nonneg (c i))).mp h t
            (Finset.mem_univ t)
    exact abs_eq_zero.mp ht
  · rintro rfl
    simp [coefficientL1]
