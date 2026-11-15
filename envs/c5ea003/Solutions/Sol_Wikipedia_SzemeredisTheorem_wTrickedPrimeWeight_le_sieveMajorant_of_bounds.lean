-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_le_sieveMajorant_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:55:22.321795+00:00
-- url     : https://prove2.me/submissions/f8cb9fec-b46b-422a-acf6-226a8fe49a90

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_normalizer_pos
import Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_le_majorant

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real













theorem maxAPForms_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < maxAPForms k := by
  exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)

theorem sieveExponent_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < sieveExponent k := by
  rw [sieveExponent]
  apply inv_pos.mpr
  exact_mod_cast
    Nat.mul_pos (by norm_num) (maxAPForms_pos hk)



theorem primeScale_pos {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 < primeScale k cutoffNormalizer := by
  rw [primeScale]
  exact lt_min (by norm_num)
    (div_pos (sieveExponent_pos hk)
      (mul_pos (by norm_num) hnorm))

theorem primeScale_nonneg {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 ≤ primeScale k cutoffNormalizer :=
  (primeScale_pos hk hnorm).le



theorem primeScale_le_sieveExponent_div
    (k : ℕ) (cutoffNormalizer : ℝ) :
    primeScale k cutoffNormalizer ≤
      sieveExponent k / (8 * cutoffNormalizer) := by
  exact min_le_right _ _



















end Wikipedia.SzemeredisTheorem

end

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



@[simp]
theorem mem_greenTaoInterval {N n : ℕ} :
    n ∈ greenTaoInterval N ↔ N / 64 ≤ n ∧ n ≤ N / 4 := by
  simp [greenTaoInterval]























end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open Filter Real

open Wikipedia.SzemeredisTheorem in
/-- Global numerical conditions sufficient for pointwise domination by the
standard smooth Selberg majorant.

The upper bound `W * N + b ≤ N²` controls every W-tricked value in a complete
residue system.  The lower logarithmic bound reserves a factor of two beyond
what is needed after using `primeScale ≤ sieveExponent / (8 * normalizer)`.
-/
theorem solution
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 3 ≤ k)
    (hN : 1 ≤ N)
    (hW : 0 < W)
    (hRtwo : 2 ≤ sieveLevel k N)
    (hRbelow : sieveLevel k N < N / 64)
    (hvalueUpper : W * N + b ≤ N ^ 2)
    (hlogLower :
      sieveExponent k / 2 * log (N : ℝ) ≤
        log (sieveLevel k N : ℝ)) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight
          (primeScale k χ.normalizer) W b n ≤
        χ.wTrickedMajorant (sieveLevel k N) W b n := by
  apply wTrickedPrimeWeight_le_majorant
    χ.normalizer_pos (by omega) hW χ.toFun
    χ.value_zero χ.zero_of_one_le
  intro n hn hp
  have hnBounds := mem_greenTaoInterval.mp hn
  have hlevelValue :
      sieveLevel k N < wTrickedValue W b n := by
    calc
      sieveLevel k N < N / 64 := hRbelow
      _ ≤ n.val := hnBounds.1
      _ ≤ W * n.val :=
        Nat.le_mul_of_pos_left n.val hW
      _ ≤ W * n.val + b := Nat.le_add_right _ _
      _ = wTrickedValue W b n := rfl
  refine ⟨hlevelValue, ?_⟩
  have hnVal : n.val ≤ N := (n.val_lt).le
  have hrepresentedUpper :
      wTrickedValue W b n ≤ N ^ 2 := by
    calc
      wTrickedValue W b n = W * n.val + b := rfl
      _ ≤ W * N + b :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left W hnVal) b
      _ ≤ N ^ 2 := hvalueUpper
  have hrepresentedUpperReal :
      (wTrickedValue W b n : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast hrepresentedUpper
  have hrepresentedPosReal :
      0 < (wTrickedValue W b n : ℝ) := by
    exact_mod_cast hp.pos
  have hlogValue :
      log (wTrickedValue W b n : ℝ) ≤
        2 * log (N : ℝ) := by
    calc
      log (wTrickedValue W b n : ℝ) ≤
          log ((N : ℝ) ^ 2) :=
        log_le_log hrepresentedPosReal hrepresentedUpperReal
      _ = 2 * log (N : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hlogN : 0 ≤ log (N : ℝ) :=
    log_nonneg (by exact_mod_cast hN)
  have hscaleNonneg :
      0 ≤ primeScale k χ.normalizer :=
    primeScale_nonneg hk χ.normalizer_pos
  have hexponentNonneg :
      0 ≤ sieveExponent k :=
    (sieveExponent_pos hk).le
  calc
    primeScale k χ.normalizer *
          log (wTrickedValue W b n : ℝ) ≤
        primeScale k χ.normalizer *
          (2 * log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogValue hscaleNonneg
    _ ≤
        (sieveExponent k / (8 * χ.normalizer)) *
          (2 * log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (primeScale_le_sieveExponent_div k χ.normalizer)
        (mul_nonneg (by norm_num) hlogN)
    _ =
        (sieveExponent k / 4 * log (N : ℝ)) /
          χ.normalizer := by
      ring
    _ ≤
        (sieveExponent k / 2 * log (N : ℝ)) /
          χ.normalizer := by
      apply (div_le_div_iff_of_pos_right χ.normalizer_pos).2
      nlinarith [mul_nonneg hexponentNonneg hlogN]
    _ ≤
        log (sieveLevel k N : ℝ) /
          χ.normalizer :=
      (div_le_div_iff_of_pos_right χ.normalizer_pos).2
        hlogLower
