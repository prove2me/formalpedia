-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.pairedDivisibilityIndicator_eq_affinePrimeProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:27:48.120504+00:00
-- url     : https://prove2.me/submissions/116d3f3f-007e-42ee-95bd-12b72040d385

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisibilityIndicator_eq_squarefreePrimeProduct

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Elementary local densities of affine forms

This starts the local-factor calculation with the exact one-form density.
An integer affine form is reduced modulo `p`; if one coefficient remains
nonzero and `p` is prime, its linear part is surjective.  All fibers then
have the same cardinality, so the zero congruence occupies exactly a
`1 / p` fraction of the finite vector space (recorded first as an exact
natural-number identity).
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm







@[simp]
theorem evalZMod_eq_zero_iff {ι : Type*} [Fintype ι]
    (p : ℕ) (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    ψ.evalZMod p x = 0 ↔
      ψ.linearMapZMod p x = -(ψ.constant : ZMod p) := by
  simp [evalZMod, eq_neg_iff_add_eq_zero, add_comm]



@[simp]
theorem mem_zeroFinsetZMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) :
    x ∈ ψ.zeroFinsetZMod p ↔ ψ.evalZMod p x = 0 := by
  simp [zeroFinsetZMod, evalZMod_eq_zero_iff]

























end AffineForm





end Wikipedia.SzemeredisTheorem

end
/-!
# Squarefree paired divisors and finite-family local factors

The Selberg expansion only receives a contribution from squarefree divisor
choices: a nonzero Möbius coefficient forces each of the two divisors attached
to every form to be squarefree.  Consequently all local least common multiples,
and their global least common multiple, are squarefree.  The canonical
prime-power CRT from `PairedDivisibilityCRT` therefore has exponent one at
every prime.

This file records that reduction exactly.  It also packages the local
intersection density of an arbitrary finite subfamily of affine forms.  The
empty, singleton, and two-element cases reduce to the exact APIs in
`LocalFactors`; the full avoidance factor is their finite
inclusion--exclusion sum.  Higher intersections require an additional
arithmetic input, so the final interface exposes that input as a hypothesis
rather than asserting an unavailable estimate.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Squarefree divisor choices -/
/-! ## Exact prime support and the squarefree indicator product -/
/-! ## Arbitrary finite-family intersection densities -/
/-! ## Exact arbitrary-family local factor formula -/
/-! ## Localization of the canonical CRT factors -/

open Wikipedia.SzemeredisTheorem in
/-- Under the explicit affine-model hypothesis, the paired indicator
separates into the canonical affine prime factors. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (values :
      κ → (ι → ZMod (pairedDivisorLcm z)) → ℕ)
    (forms : κ → AffineForm ι ℤ)
    (hz : SquarefreePairedDivisorChoice z)
    (hmodel :
      PairedDivisibilityHasAffinePrimeModels
        z values forms hz)
    (x : ι → ZMod (pairedDivisorLcm z)) :
    pairedDivisibilityIndicator values z x =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affinePairedPrimeFactor forms z hz p
          (coordinatePrimePowerEquiv x p) := by
  rw [pairedDivisibilityIndicator_eq_squarefreePrimeProduct
    values z hz x]
  apply Finset.prod_congr rfl
  intro p _hp
  unfold squarefreePairedPrimeIndicator
    affinePairedPrimeFactor affineFamilyZeroProduct
  apply Finset.prod_congr rfl
  intro q hq
  have hiff := hmodel x p q hq
  change natDivisibilityIndicator (p : ℕ) (values q x) =
    finsetIndicator ((forms q).zeroFinsetZMod (p : ℕ))
      (squarefreePrimePowerEquiv hz p
        (coordinatePrimePowerEquiv x p))
  by_cases hpvalue : (p : ℕ) ∣ values q x
  · have heval := hiff.mp hpvalue
    simpa [natDivisibilityIndicator, hpvalue, finsetIndicator,
      squarefreeCanonicalPrimeComponent] using heval
  · have heval : ¬
        (forms q).evalZMod (p : ℕ)
          (squarefreeCanonicalPrimeComponent hz p x) = 0 :=
      fun hzero => hpvalue (hiff.mpr hzero)
    simpa [natDivisibilityIndicator, hpvalue, finsetIndicator,
      squarefreeCanonicalPrimeComponent] using heval
