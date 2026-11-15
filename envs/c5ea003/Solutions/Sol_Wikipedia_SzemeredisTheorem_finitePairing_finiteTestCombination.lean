-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.finitePairing_finiteTestCombination
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:05:01.746105+00:00
-- url     : https://prove2.me/submissions/78ae6954-acb0-486e-a0e9-b38a9f6dd306

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
/-- Pairing distributes across a finite linear combination of tests. -/
theorem solution
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (f : Ω → ℝ) (q : τ → Ω → ℝ) (c : τ → ℝ) :
    finitePairing f (finiteTestCombination q c) =
      ∑ t, c t * finitePairing f (q t) := by
  rw [finiteTestCombination]
  unfold finitePairing mean
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Fintype.sum_congr
  intro t
  calc
    (Finset.univ.expect fun x => f x * (c t * q t x)) =
        Finset.univ.expect (fun x => c t * (f x * q t x)) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = c t *
        Finset.univ.expect (fun x => f x * q t x) := by
      exact (Finset.mul_expect Finset.univ
        (fun x => f x * q t x) (c t)).symm
