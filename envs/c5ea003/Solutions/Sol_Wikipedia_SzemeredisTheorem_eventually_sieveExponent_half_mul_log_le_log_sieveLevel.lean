-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eventually_sieveExponent_half_mul_log_le_log_sieveLevel
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:51:10.44791+00:00
-- url     : https://prove2.me/submissions/0e95b6f0-cd02-49d1-ae17-0de11df95337

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
/-- The natural floor in `sieveLevel` loses only a negligible additive
constant in the logarithm.  Eventually at least half of the nominal
`sieveExponent * log N` remains. -/
theorem solution
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop,
      sieveExponent k / 2 * log (N : ℝ) ≤
        log (sieveLevel k N : ℝ) := by
  have hexponent : 0 < sieveExponent k :=
    sieveExponent_pos hk
  have hlog :
      Tendsto (fun N : ℕ => log (N : ℝ))
        atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge :
      ∀ᶠ N : ℕ in atTop,
        2 * log 2 / sieveExponent k ≤
          log (N : ℝ) :=
    hlog.eventually
      (eventually_ge_atTop
        (2 * log 2 / sieveExponent k))
  filter_upwards [
    hlogLarge,
    eventually_two_le_sieveLevel hk,
    eventually_gt_atTop 0] with N hlarge hRtwo hN
  have hNposReal : 0 < (N : ℝ) := by
    positivity
  have hrpowPos :
      0 < (N : ℝ) ^ sieveExponent k :=
    Real.rpow_pos_of_pos hNposReal _
  have hrpowTwo :
      (2 : ℝ) ≤ (N : ℝ) ^ sieveExponent k := by
    have htwoFloor :
        (2 : ℝ) ≤ (sieveLevel k N : ℝ) := by
      exact_mod_cast hRtwo
    exact htwoFloor.trans
      (Nat.floor_le hrpowPos.le)
  have hfloor :
      (N : ℝ) ^ sieveExponent k - 1 <
        (sieveLevel k N : ℝ) := by
    simpa only [sieveLevel] using
      (Nat.sub_one_lt_floor
        ((N : ℝ) ^ sieveExponent k))
  have hhalfFloor :
      (N : ℝ) ^ sieveExponent k / 2 ≤
        (sieveLevel k N : ℝ) := by
    have :
        (N : ℝ) ^ sieveExponent k / 2 ≤
          (N : ℝ) ^ sieveExponent k - 1 := by
      linarith
    exact this.trans hfloor.le
  have hlogFloor :
      log ((N : ℝ) ^ sieveExponent k / 2) ≤
        log (sieveLevel k N : ℝ) :=
    log_le_log (div_pos hrpowPos (by norm_num))
      hhalfFloor
  have hlogIdentity :
      log ((N : ℝ) ^ sieveExponent k / 2) =
        sieveExponent k * log (N : ℝ) - log 2 := by
    rw [Real.log_div hrpowPos.ne' (by norm_num),
      Real.log_rpow hNposReal]
  have hlarge' :
      2 * log 2 ≤
        log (N : ℝ) * sieveExponent k :=
    (div_le_iff₀ hexponent).mp hlarge
  rw [hlogIdentity] at hlogFloor
  nlinarith
