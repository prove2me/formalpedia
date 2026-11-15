-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:09:08.178018+00:00
-- url     : https://prove2.me/theorems/b950fb47-a077-4c85-8e65-e59747475480
-- title:
--   LCM-weighted divisor mass and the selected cyclic divisor sum
-- statement:
--   For a real cutoff function $\chi$, a natural level $R$, and a finite family of form indices, the LCM mass sums the absolute paired-divisor coefficient times the least common multiple of all chosen divisors over the finite choices bounded by $R$.
--
--   For a structured smooth cutoff, a positive cyclic modulus, natural $W,b$, and a Boolean-selected CFZ family, the cyclic divisor sum instead weights each paired-divisor coefficient by the normalized density of its simultaneous divisibility conditions on the natural $W$-tricked form values. Thus it retains the actual cyclic divisibility constraints rather than replacing them by an Euler approximation. The first object is a nonnegative error-control mass; the second is a signed exact expansion sum.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCarryDivisorExpansion.lean#L37-L105

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Lean
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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Summing the CFZ carry-block error through the divisor expansion

For a selected CFZ family with `m` forms, every smooth paired-divisor choice
has global LCM

`D ≤ R ^ (2 * m)`.

Consequently the hypothesis `R ^ (2 * m) ≤ N` makes the carry-block Euler
comparison available for every supported term.  A term with nonsquarefree
divisors has zero Möbius coefficient, so it disappears before the
squarefree CRT theorem is invoked.

This file first retains the sharp finite error mass

`∑ z, |coefficient z| * pairedDivisorLcm z`.

Discarding the coefficient and bounding both the number of choices and every
LCM by `R ^ (2 * m)` gives the explicit, deliberately crude loss

`C_{k,m} * R ^ (4 * m) / N`.

The block Euler product is kept inside the average over quotient blocks.
No common Euler product across carry blocks is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-! ## LCM mass of the finite divisor expansion -/

/-- The coefficient-weighted LCM mass of a smooth paired-divisor family. -/
noncomputable def smoothDivisorFamilyLcmMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : ℝ → ℝ) (R : ℕ) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices κ R,
    |smoothDivisorFamilyCoefficient χ R z| *
      (pairedDivisorLcm z : ℝ)





/-! ## The unscaled selected-family divisor sums -/

/-- The actual cyclic paired-divisibility sum in the selected Selberg
expansion. -/
noncomputable def selectedCFZCyclicDivisorSum
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices
        (SelectedCFZFormIndex e) R,
    smoothDivisorFamilyCoefficient χ.toFun R z *
      pairedDivisibilityDensity
        (fun q : SelectedCFZFormIndex e =>
          fun x : CubePoint k N =>
            cfzWTrickedLinearValue W b q.1 x)
        z



namespace SmoothSieveCutoff









/-! ## Reinsert the normalized Selberg prefactor -/







end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.selectedCFZCyclicDivisorSum.congr_simp,
    `Wikipedia.SzemeredisTheorem.smoothDivisorFamilyLcmMass.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


