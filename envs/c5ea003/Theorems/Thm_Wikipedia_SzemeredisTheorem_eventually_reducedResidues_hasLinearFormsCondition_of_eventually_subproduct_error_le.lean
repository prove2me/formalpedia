-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_reducedResidues_hasLinearFormsCondition_of_eventually_subproduct_error_le
-- name    : Wikipedia.SzemeredisTheorem.eventually_reducedResidues_hasLinearFormsCondition_of_eventually_subproduct_error_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:54:19.771208+00:00
-- url     : https://prove2.me/theorems/7fb6b196-3a6b-4c46-b074-f8274c55566b
-- title:
--   Pointwise eventual subproduct bounds give a uniform linear-forms condition
-- statement:
--   Fix natural $k,W$ and a family $\nu_{M,b}$ of real functions on $\mathbb Z/(M+1)\mathbb Z$. If for every reduced residue $b$ modulo $W$ and every Boolean CFZ exponent pattern the selected-product mean is eventually within absolute error $\eta$ of $1$, then a common eventual range of $M$ satisfies the $k$-linear-forms condition with the same error $\eta$ for every reduced residue.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ReducedResidueCyclicLinearFormsAssembly.lean#L24-L65

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

theorem
    Wikipedia.SzemeredisTheorem.eventually_reducedResidues_hasLinearFormsCondition_of_eventually_subproduct_error_le
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
          k (M + 1) (ν M b) η := by sorry
