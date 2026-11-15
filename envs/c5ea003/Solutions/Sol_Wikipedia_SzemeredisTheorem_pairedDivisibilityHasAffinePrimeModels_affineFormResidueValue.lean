-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.pairedDivisibilityHasAffinePrimeModels_affineFormResidueValue
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:46:36.342259+00:00
-- url     : https://prove2.me/submissions/fb31ada0-b344-4b3b-a972-66a1f400ceb8

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_castHom_affineForm_evalZMod
import Theorems.Thm_Wikipedia_SzemeredisTheorem_squarefreeCanonicalPrimeComponent_apply_eq_castHom

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Carry-block Euler products for selected CFZ families

The cyclic CFZ lift is not globally periodic modulo a paired divisor LCM:
crossing a representative boundary changes an integer carry.  The preceding
carry-block boundary file replaces that false periodicity by a sound
piecewise-affine model.  This file identifies the exact arithmetic model on
each complete quotient block.

For `D = pairedDivisorLcm z`, a complete block has the form

`x = r + D a`,  with `0 ≤ r_v < D`.

The carry is frozen at the lower corner `D a`.  Thus the block is governed
by the family

`q ↦ cfzCarryAdjustedAffineForm N W b q (cfzCarry q (D a))`.

Its mean over `r` is an exact squarefree CRT Euler product.  Averaging those
products over all complete blocks gives the global blockwise Euler model.
The only losses in comparing it with the original cyclic density are:

* the explicit carry-transition density from `CFZCarryBlockBoundary`;
* the outer partial-block boundary of size
  `O(D * card(CFZVariable k) / N)`.

The affine constants may depend arbitrarily on the block and on the form.
At primes dividing `W` they are still congruent to the reduced residue `b`,
so every supported local density is zero.  At good primes outside `W`,
one-form and rank-two geometry depends only on the coefficients, giving the
usual exact cardinality-at-most-two formula and the uniform `p⁻²` bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic natural representative for an affine residue -/



@[simp]
theorem natCast_affineFormResidueValue
    {ι : Type*} [Fintype ι] {D : ℕ} [NeZero D]
    (ψ : AffineForm ι ℤ) (x : ι → ZMod D) :
    (affineFormResidueValue ψ x : ZMod D) =
      ψ.evalZMod D x :=
  ZMod.natCast_zmod_val _





/-! ## Complete quotient blocks and their affine families -/









/-! ## Good complete quotient blocks -/













/-! ## Exact blockwise CRT and averaged Euler products -/







/-! ## The complete-block mean is the averaged Euler product -/



/-! ## The outer partial-block boundary -/







/-! ## Unconditional cyclic-to-Euler approximation -/









/-! ## Selected-family specialization -/









/-! ## Carry-dependent constants and primes dividing `W` -/



















/-! ## Good primes outside `W` -/



















end Wikipedia.SzemeredisTheorem

end
/-!
# Carry-block Euler products for selected CFZ families

The cyclic CFZ lift is not globally periodic modulo a paired divisor LCM:
crossing a representative boundary changes an integer carry.  The preceding
carry-block boundary file replaces that false periodicity by a sound
piecewise-affine model.  This file identifies the exact arithmetic model on
each complete quotient block.

For `D = pairedDivisorLcm z`, a complete block has the form

`x = r + D a`,  with `0 ≤ r_v < D`.

The carry is frozen at the lower corner `D a`.  Thus the block is governed
by the family

`q ↦ cfzCarryAdjustedAffineForm N W b q (cfzCarry q (D a))`.

Its mean over `r` is an exact squarefree CRT Euler product.  Averaging those
products over all complete blocks gives the global blockwise Euler model.
The only losses in comparing it with the original cyclic density are:

* the explicit carry-transition density from `CFZCarryBlockBoundary`;
* the outer partial-block boundary of size
  `O(D * card(CFZVariable k) / N)`.

The affine constants may depend arbitrarily on the block and on the form.
At primes dividing `W` they are still congruent to the reduced residue `b`,
so every supported local density is zero.  At good primes outside `W`,
one-form and rank-two geometry depends only on the coefficients, giving the
usual exact cardinality-at-most-two formula and the uniform `p⁻²` bound.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## A generic natural representative for an affine residue -/

open Wikipedia.SzemeredisTheorem in
/-- Natural representatives of arbitrary affine residues satisfy the prime
model required by the squarefree paired CRT theorem. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    PairedDivisibilityHasAffinePrimeModels z
      (fun q => affineFormResidueValue (forms q))
      forms hz := by
  intro x p q _hq
  have hpD :
      (p : ℕ) ∣ pairedDivisorLcm z :=
    Nat.dvd_of_mem_primeFactors p.2
  have hvalue :
      (affineFormResidueValue (forms q) x : ZMod (p : ℕ)) =
        (forms q).evalZMod (p : ℕ)
          (squarefreeCanonicalPrimeComponent hz p x) := by
    calc
      (affineFormResidueValue (forms q) x : ZMod (p : ℕ)) =
          ZMod.castHom hpD (ZMod (p : ℕ))
            (affineFormResidueValue (forms q) x :
              ZMod (pairedDivisorLcm z)) := by
            symm
            exact
              map_natCast
                (ZMod.castHom hpD (ZMod (p : ℕ)))
                (affineFormResidueValue (forms q) x)
      _ = ZMod.castHom hpD (ZMod (p : ℕ))
            ((forms q).evalZMod (pairedDivisorLcm z) x) := by
          rw [natCast_affineFormResidueValue]
      _ = (forms q).evalZMod (p : ℕ)
            (fun i =>
              ZMod.castHom hpD (ZMod (p : ℕ)) (x i)) :=
          castHom_affineForm_evalZMod hpD (forms q) x
      _ = (forms q).evalZMod (p : ℕ)
            (squarefreeCanonicalPrimeComponent hz p x) := by
          congr 1
          funext i
          exact
            (squarefreeCanonicalPrimeComponent_apply_eq_castHom
              hz p x i).symm
  rw [← ZMod.natCast_eq_zero_iff, hvalue]
