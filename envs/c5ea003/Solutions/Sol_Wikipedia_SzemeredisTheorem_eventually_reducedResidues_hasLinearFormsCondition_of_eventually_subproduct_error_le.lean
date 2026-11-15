-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eventually_reducedResidues_hasLinearFormsCondition_of_eventually_subproduct_error_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:50:16.094278+00:00
-- url     : https://prove2.me/submissions/e5fd8641-f30b-4a8c-ae0a-6ec8e3977638

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
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
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Reduced-residue cyclic linear-forms assembly

The analytic sieve estimates one fixed reduced residue and one fixed
Boolean-selected subproduct at a time.  Both indexing types are finite once
the `W`-trick modulus and the number of forms have been fixed.  This file
records the exact finite-intersection step needed by the final sieve:
eventual non-strict error bounds are retained unchanged, without passing
through a `Tendsto` statement and without requiring estimates for residues
that are not coprime to `W`.

The second theorem packages the triangle step used when the cyclic
subproduct mean is first compared with a complex Euler main term, and that
main term is then compared with one.
-/
open Wikipedia.SzemeredisTheorem
open Filter

open Wikipedia.SzemeredisTheorem in
/-- Pointwise eventual error bounds for every reduced residue and every
Boolean exponent have a common eventual range on which the linear-forms
condition holds for all reduced residues.

This is only a finite-intersection argument.  In particular, the input
bound `≤ η` is passed to `HasLinearFormsCondition` without weakening it to a
strict bound or deriving it from convergence. -/
theorem
    solution
    {k W : ℕ}
    (ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ)
    {η : ℝ}
    (herror :
      ∀ b, b ∈ reducedResidues W →
        ∀ e : LinearFormsExponent k,
          ∀ᶠ M : ℕ in atTop,
            |mean
                  (linearFormsProduct k (M + 1)
                    (ν M b) e) -
                1| ≤ η) :
    ∀ᶠ M : ℕ in atTop,
      ∀ b, b ∈ reducedResidues W →
        HasLinearFormsCondition
          k (M + 1) (ν M b) η := by
  have hresidue :
      ∀ b : ↥(reducedResidues W),
        ∀ᶠ M : ℕ in atTop,
          HasLinearFormsCondition
            k (M + 1) (ν M b) η := by
    intro b
    exact
      Filter.eventually_all.mpr
        (herror b b.property)
  have hall :
      ∀ᶠ M : ℕ in atTop,
        ∀ b : ↥(reducedResidues W),
          HasLinearFormsCondition
            k (M + 1) (ν M b) η :=
    Filter.eventually_all.mpr hresidue
  filter_upwards [hall] with M hM
  intro b hb
  exact hM ⟨b, hb⟩
