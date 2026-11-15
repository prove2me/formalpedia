-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_offDiagMass_pos_of_count_lower
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:59:10.286265+00:00
-- url     : https://prove2.me/submissions/e652985c-b6b5-487a-8837-f2f835ac74bb

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Assembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Archimedean
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
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPOffDiagMass_pos_of_count_lower_height
import Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_le_two_mul_alpha_mul_log

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/

namespace Wikipedia.SzemeredisTheorem













theorem wTrickedPrimeWeight_nonneg {N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 ≤ α) (W b : ℕ) (n : ZMod N) :
    0 ≤ wTrickedPrimeWeight α W b n := by
  unfold wTrickedPrimeWeight
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg hα
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h.2.ne_zero)))
  · exact le_rfl













end Wikipedia.SzemeredisTheorem

end
/-!
# Negligibility of diagonal progressions

The relative-counting argument produces a positive lower bound for the
normalized count of cyclic progressions.  To extract a progression with
nonzero common difference, that lower bound must dominate the contribution
of the constant progressions.

For the W-tricked prime weight the pointwise height is at most a fixed
multiple of `log N`.  Since every fixed power of `log N` is `o(N)`, the
diagonal contribution is eventually smaller than any fixed positive
progression-count lower bound.  This file records that elementary bridge
without imposing any sieve or transference hypotheses.
-/
open Wikipedia.SzemeredisTheorem
open Filter

open Wikipedia.SzemeredisTheorem in
/-- Specialization of the preceding extraction lemma to the W-tricked prime
weight and its logarithmic height bound. -/
theorem solution
    {k N W b : ℕ} [NeZero N] {α c : ℝ}
    (hk : 1 ≤ k)
    (hα : 0 ≤ α) (hW : 0 < W)
    (hN : 1 ≤ N) (hWB : W + b ≤ N)
    (hcountLower :
      c ≤ cyclicAPCount k N
        (wTrickedPrimeWeight α W b))
    (hheight :
      (2 * α * Real.log (N : ℝ)) ^ k <
        (N : ℝ) * c) :
    0 < cyclicAPOffDiagMass k N
      (wTrickedPrimeWeight α W b) := by
  apply cyclicAPOffDiagMass_pos_of_count_lower_height
    hk
    (wTrickedPrimeWeight_nonneg hα W b)
    (wTrickedPrimeWeight_le_two_mul_alpha_mul_log
      hα hW hN hWB)
  · have hlogNonneg : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hN
    positivity
  · exact hcountLower
  · exact hheight
