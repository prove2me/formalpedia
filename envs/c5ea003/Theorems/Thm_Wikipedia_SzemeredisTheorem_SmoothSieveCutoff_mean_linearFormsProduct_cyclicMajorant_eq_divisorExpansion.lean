-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_mean_linearFormsProduct_cyclicMajorant_eq_divisorExpansion
-- name    : Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.mean_linearFormsProduct_cyclicMajorant_eq_divisorExpansion
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:37:26.951705+00:00
-- url     : https://prove2.me/theorems/c3fc3026-1b86-49ae-b011-311dcb8fe91a
-- title:
--   The selected cyclic linear-forms product has an exact divisor expansion
-- statement:
--   Let $N\ne0$, $\chi$ be a smooth sieve cutoff, $R>1$, $b>0$, and $W\in\mathbb N$. For a Boolean CFZ pattern $e$ selecting $m$ forms, the mean cyclic-majorant product equals $S^m(\log R)^{2m}$ times the sum over supported paired-divisor families $z$ of their smooth coefficient times the paired divisibility density of the selected W-tricked forms, where $S$ is the normalized Selberg scale for $\chi,R,W$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CyclicMajorant.lean#L150-L190

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
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
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# The global cyclic Selberg majorant

The prime weight is localized to `greenTaoInterval` in order to unwrap a
positive cyclic progression at the end of the proof.  Its transference
majorant does not need the same localization: outside the interval the prime
weight is zero, so any nonnegative majorant is sufficient.

Keeping the smooth Selberg majorant on the whole standard residue system
removes interval indicators from the linear-forms estimate.  This file
defines that global cyclic majorant, proves pointwise domination from the
existing localized theorem, and reindexes every Boolean CFZ subproduct as a
product over its selected subtype.  The latter is the exact interface needed
to apply the generic finite divisor and Fourier expansions to every exponent
tested by `HasLinearFormsCondition`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.mean_linearFormsProduct_cyclicMajorant_eq_divisorExpansion
    {k N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R W b : ℕ} (hR : 1 < R) (hb : 0 < b)
    (e : LinearFormsExponent k) :
    mean
        (linearFormsProduct k N
          (χ.cyclicMajorant R W b) e) =
      normalizedSelbergScale χ.normalizer R W ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((Real.log R ^ 2) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∑ z ∈ smoothDivisorFamilyChoices
              (SelectedCFZFormIndex e) R,
            smoothDivisorFamilyCoefficient χ.toFun R z *
              pairedDivisibilityDensity
                (fun q : SelectedCFZFormIndex e =>
                  cfzWTrickedLinearValue
                    (k := k) (N := N) W b q.1) z) := by sorry
