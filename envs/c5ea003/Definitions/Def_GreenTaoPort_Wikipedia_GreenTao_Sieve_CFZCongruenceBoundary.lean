-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:05:27.906167+00:00
-- url     : https://prove2.me/theorems/dc9f8ef7-ad03-41ea-ac6c-9bcd05fc7cd4
-- title:
--   Natural-box coordinates and integer carries for CFZ forms
-- statement:
--   A natural doubled-variable vector is reduced coordinatewise to the cyclic CFZ cube. For a positive modulus $N$, the carry of an integer CFZ form at a natural point $x$ is its integer value divided by $N$ using integer Euclidean quotient; subtracting $N$ times this carry leaves the standard residue.
--
--   The bundle also gives the explicit coordinatewise bijections between a typed natural residue box of positive side length and a vector over the corresponding cyclic group. In the CFZ specialization this identifies the doubled natural box with the doubled cyclic cube, using standard representatives for the inverse maps.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCongruenceBoundary.lean#L103-L474

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Finite-box congruence boundaries for the CFZ divisor expansion

This file isolates the exact finite-box step between the divisor expansion
and the prime-local arithmetic.  It has three layers.

* A normalized boundary estimate compares a bounded periodic function on a
  natural box with its exact residue-class mean.
* Coordinatewise `Fin`/`ZMod` equivalences identify the mean on a
  `CubePoint k N` with the corresponding natural box mean.
* For the cyclic representative used by `cfzWTrickedLinearValue`, periodicity
  modulo a divisor modulus `D` is proved under the precise compatibility
  hypothesis `D ∣ W * N`.

The compatibility hypothesis in the last item is mathematically necessary
for this direct rectangular trimming argument: reducing a form modulo `N`
can change an integer lift by a multiple of `N`, and the subsequent
`W`-trick changes its value by a multiple of `W * N`.  Without divisibility
by `D`, an unconditional treatment must subdivide the box into carry cells
on which every modular reduction has a fixed integer lift.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Why cyclic representatives need a compatibility or carry argument -/





/-! ## Weighted lifts through two moduli -/



/-! ## Natural representatives of CFZ cube points -/

/-- Interpret a natural vector as a doubled CFZ variable vector modulo `N`. -/
def cubePointOfNat {k N : ℕ}
    (x : CFZVariable k → ℕ) : CubePoint k N :=
  fun i b => (x (i, b) : ZMod N)







/-! ## Canonical carry cells -/

/-- The integer carry made when an integer CFZ affine form is reduced to its
standard representative modulo `N`. -/
def cfzCarry
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ) : ℤ :=
  (cfzAffineForm q).eval (fun v => (x v : ℤ)) / (N : ℤ)















/-! ## Divisibility indicators modulo a common multiple -/







/-! ## Exact finite-box and residue-vector reindexing -/



/-- Standard representatives give an explicit equivalence between a typed
natural residue box and a vector over `ZMod D`. -/
def finiteBoxEquivZModVector
    {ι : Type*} (D : ℕ) [NeZero D] :
    FiniteBox (fun _ : ι => D) ≃ (ι → ZMod D) where
  toFun x i := (x i : ℕ)
  invFun x i := ⟨(x i).val, (x i).val_lt⟩
  left_inv x := by
    funext i
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (x i).isLt
  right_inv x := by
    funext i
    exact ZMod.natCast_zmod_val (x i)







/-! ## Reindexing the cyclic CFZ cube -/

/-- Standard coordinate representatives identify the natural box of side
`N` with the doubled cyclic CFZ cube. -/
def finiteBoxEquivCubePoint
    (k N : ℕ) [NeZero N] :
    FiniteBox (fun _ : CFZVariable k => N) ≃ CubePoint k N where
  toFun x i b := (x (i, b) : ℕ)
  invFun x v := ⟨(x v.1 v.2).val, (x v.1 v.2).val_lt⟩
  left_inv x := by
    funext v
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (x v).isLt
  right_inv x := by
    funext i b
    exact ZMod.natCast_zmod_val (x i b)





/-! ## CFZ periodicity under lift compatibility -/







/-! ## The exact affine residue model -/













/-! ## Normalized trimming loss -/







/-! ## Paired divisibility specialization -/









end Wikipedia.SzemeredisTheorem


