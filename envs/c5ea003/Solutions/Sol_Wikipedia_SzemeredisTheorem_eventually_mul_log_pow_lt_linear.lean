-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eventually_mul_log_pow_lt_linear
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:50:16.113777+00:00
-- url     : https://prove2.me/submissions/df58bfa3-b58b-4a26-b746-de4820dc25e4

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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
/-- Every fixed multiple of a fixed power of `log N` is eventually smaller
than `c N` for any `c > 0`.  The constant `C` is unrestricted: the absolute
value estimate supplied by little-o is stronger than the displayed
one-sided inequality. -/
theorem solution
    (C c : ℝ) (k : ℕ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      (C * Real.log (N : ℝ)) ^ k < (N : ℝ) * c := by
  have hlittle :
      (fun N : ℕ => (C * Real.log (N : ℝ)) ^ k) =o[atTop]
        (fun N : ℕ => (N : ℝ)) := by
    have hlog :
        (fun N : ℕ => Real.log (N : ℝ) ^ k) =o[atTop]
          (fun N : ℕ => (N : ℝ)) :=
      (Real.isLittleO_pow_log_id_atTop (n := k)).comp_tendsto
        tendsto_natCast_atTop_atTop
    simpa [mul_pow] using hlog.const_mul_left (C ^ k)
  have hcHalf : 0 < c / 2 := by positivity
  filter_upwards
    [hlittle.bound hcHalf, eventually_gt_atTop (0 : ℕ)]
      with N hbound hN
  calc
    (C * Real.log (N : ℝ)) ^ k ≤
        ‖(C * Real.log (N : ℝ)) ^ k‖ :=
      (by simpa [Real.norm_eq_abs] using
        le_abs_self ((C * Real.log (N : ℝ)) ^ k))
    _ ≤ (c / 2) * ‖(N : ℝ)‖ := hbound
    _ = (c / 2) * (N : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
    _ < (N : ℝ) * c := by
      have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      nlinarith
