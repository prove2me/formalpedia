-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eventually_sieveLevel_lt_div_sixtyFour
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:51:10.510192+00:00
-- url     : https://prove2.me/submissions/8b010471-12dc-44f9-846d-7bbef8610041

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





















/-- The sieve level tends to infinity for every progression length in the
nontrivial range. -/
theorem tendsto_sieveLevel_atTop {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (sieveLevel k) atTop atTop := by
  change Tendsto
    (fun N : ℕ ↦ ⌊(N : ℝ) ^ sieveExponent k⌋₊)
    atTop atTop
  simpa [Function.comp_def] using
    tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (sieveExponent_pos hk)).comp
        tendsto_natCast_atTop_atTop)



theorem eventually_two_le_sieveLevel {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ sieveLevel k N :=
  (tendsto_sieveLevel_atTop hk).eventually
    (eventually_ge_atTop 2)



end Wikipedia.SzemeredisTheorem

end

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

theorem sieveExponent_lt_one {k : ℕ} (hk : 3 ≤ k) :
    sieveExponent k < 1 := by
  rw [sieveExponent]
  apply inv_lt_one_of_one_lt₀
  have hmax : 1 ≤ maxAPForms k :=
    maxAPForms_pos hk
  exact_mod_cast (show 1 < 100 * maxAPForms k by omega)















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
/-- The chosen sublinear sieve level eventually lies below the left endpoint
of the localization interval. -/
theorem solution
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop,
      sieveLevel k N < N / 64 := by
  have hgap : 0 < 1 - sieveExponent k := by
    linarith [sieveExponent_lt_one hk]
  have hratio :
      Tendsto
        (fun N : ℕ =>
          (N : ℝ) ^ (sieveExponent k - 1))
        atTop (nhds 0) := by
    have h :=
      (tendsto_rpow_neg_atTop hgap).comp
        tendsto_natCast_atTop_atTop
    convert h using 1
    funext N
    congr 1
    ring
  have hratioSmall :
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (sieveExponent k - 1) <
          (1 : ℝ) / 128 :=
    (tendsto_order.1 hratio).2 _ (by norm_num)
  filter_upwards [
    hratioSmall,
    eventually_two_le_sieveLevel hk,
    eventually_gt_atTop 128] with N hsmall hRtwo hN
  have hNposReal : 0 < (N : ℝ) := by
    positivity
  have hrpow :
      (N : ℝ) ^ sieveExponent k <
        (N : ℝ) / 128 := by
    calc
      (N : ℝ) ^ sieveExponent k =
          (N : ℝ) ^
            ((sieveExponent k - 1) + 1) := by
        apply congrArg (fun z : ℝ => (N : ℝ) ^ z)
        ring
      _ =
          (N : ℝ) ^ (sieveExponent k - 1) *
            (N : ℝ) := by
        rw [Real.rpow_add hNposReal, Real.rpow_one]
      _ < ((1 : ℝ) / 128) * (N : ℝ) :=
        mul_lt_mul_of_pos_right hsmall hNposReal
      _ = (N : ℝ) / 128 := by ring
  have hfloor :
      (sieveLevel k N : ℝ) ≤
        (N : ℝ) ^ sieveExponent k := by
    exact Nat.floor_le
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hscaledReal :
      (128 * sieveLevel k N : ℝ) < (N : ℝ) := by
    nlinarith
  have hscaledNat :
      128 * sieveLevel k N < N := by
    exact_mod_cast hscaledReal
  omega
