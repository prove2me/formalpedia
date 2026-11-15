-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_le_two_mul_alpha_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:57:46.717634+00:00
-- url     : https://prove2.me/submissions/deb50ce3-408d-4d0c-ae56-8848451396a2

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

section



/-!
# Assembly-facing prime-weight majorization

The pointwise Selberg majorization theorem reduces its substantive case to
two scalar inequalities: the sieve level lies below the represented prime,
and the scaled logarithm of that prime is at most
`log R / χ.normalizer`.

This file derives both inequalities from global bounds that are independent
of the residue `n`.  The remaining eventual parameter argument only has to
establish those four global bounds for `R = sieveLevel k N`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real







/-- A fixed affine coefficient and shift are absorbed by `N²` once their
sum is at most `N`. -/
theorem affine_mul_add_le_sq
    {W b N : ℕ} (hN : 1 ≤ N) (hWB : W + b ≤ N) :
    W * N + b ≤ N ^ 2 := by
  calc
    W * N + b ≤ W * N + b * N := by
      exact Nat.add_le_add_left
        (Nat.le_mul_of_pos_right b (Nat.zero_lt_of_lt hN))
        (W * N)
    _ = (W + b) * N := by ring
    _ ≤ N * N := Nat.mul_le_mul_right N hWB
    _ = N ^ 2 := by ring









end Wikipedia.SzemeredisTheorem

end

section




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

namespace Wikipedia.SzemeredisTheorem

open Filter

/-- A W-tricked value in the standard residue system is bounded by the value
at the right endpoint of that system. -/
theorem wTrickedValue_le_affine_end
    {N : ℕ} [NeZero N] (W b : ℕ) (n : ZMod N) :
    wTrickedValue W b n ≤ W * N + b := by
  unfold wTrickedValue
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left W n.val_lt.le) b

/-- The real totient ratio is at most one for a positive modulus. -/
theorem totient_div_self_le_one
    {W : ℕ} (hW : 0 < W) :
    (W.totient : ℝ) / W ≤ 1 := by
  rw [div_le_one (by exact_mod_cast hW)]
  exact_mod_cast Nat.totient_le W













/-! ## Asymptotic final interface -/







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
/-- Under the standard parameter bound `W + b ≤ N`, the W-tricked prime
weight has the crude but uniform height bound `2 α log N`.

The localization to `greenTaoInterval` is not needed for this estimate; only
the standard representative bound `n.val < N` is used. -/
theorem solution
    {N W b : ℕ} [NeZero N] {α : ℝ}
    (hα : 0 ≤ α) (hW : 0 < W)
    (hN : 1 ≤ N) (hWB : W + b ≤ N)
    (n : ZMod N) :
    wTrickedPrimeWeight α W b n ≤
      2 * α * Real.log (N : ℝ) := by
  unfold wTrickedPrimeWeight
  split_ifs with hprime
  · have hvaluePos :
        (0 : ℝ) < (wTrickedValue W b n : ℝ) := by
      exact_mod_cast hprime.2.pos
    have hvalueUpperNat :
        wTrickedValue W b n ≤ N ^ 2 :=
      (wTrickedValue_le_affine_end W b n).trans
        (affine_mul_add_le_sq hN hWB)
    have hvalueUpperReal :
        (wTrickedValue W b n : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast hvalueUpperNat
    have hlog :
        Real.log (wTrickedValue W b n) ≤
          2 * Real.log (N : ℝ) := by
      calc
        Real.log (wTrickedValue W b n) ≤
            Real.log ((N : ℝ) ^ 2) :=
          Real.log_le_log hvaluePos hvalueUpperReal
        _ = 2 * Real.log (N : ℝ) := by
          rw [Real.log_pow]
          norm_num
    have hratioNonneg :
        0 ≤ (W.totient : ℝ) / W :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hratio :
        (W.totient : ℝ) / W ≤ 1 :=
      totient_div_self_le_one hW
    have hlogNonneg : 0 ≤ 2 * Real.log (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      positivity
    calc
      α * ((W.totient : ℝ) / W) *
            Real.log (wTrickedValue W b n) ≤
          α * ((W.totient : ℝ) / W) *
            (2 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog
          (mul_nonneg hα hratioNonneg)
      _ ≤ α * (2 * Real.log (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hα hratio) hlogNonneg
      _ = 2 * α * Real.log (N : ℝ) := by ring
  · have hlogNonneg : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hN
    positivity
