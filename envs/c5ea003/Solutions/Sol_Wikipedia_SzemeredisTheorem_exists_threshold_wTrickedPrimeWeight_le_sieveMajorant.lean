-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_threshold_wTrickedPrimeWeight_le_sieveMajorant
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:56:47.472769+00:00
-- url     : https://prove2.me/submissions/9bf2bb6b-2c65-4c0c-a120-ee2fa4928c59

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_sieveExponent_half_mul_log_le_log_sieveLevel
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_sieveLevel_lt_div_sixtyFour
import Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_le_sieveMajorant_of_bounds

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



/-- Convenient specialization in which the affine upper bound follows from
the single eventual threshold `W + b ≤ N`. -/
theorem wTrickedPrimeWeight_le_sieveMajorant_of_add_le
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 3 ≤ k)
    (hN : 1 ≤ N)
    (hW : 0 < W)
    (hWB : W + b ≤ N)
    (hRtwo : 2 ≤ sieveLevel k N)
    (hRbelow : sieveLevel k N < N / 64)
    (hlogLower :
      sieveExponent k / 2 * log (N : ℝ) ≤
        log (sieveLevel k N : ℝ)) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight
          (primeScale k χ.normalizer) W b n ≤
        χ.wTrickedMajorant (sieveLevel k N) W b n :=
  wTrickedPrimeWeight_le_sieveMajorant_of_bounds
    χ hk hN hW hRtwo hRbelow
    (affine_mul_add_le_sq hN hWB) hlogLower





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
/-- Threshold form of eventual pointwise majorization for fixed `W` and
shift `b`.  This is the form consumed by the final nested parameter
selection after the W-trick cutoff has been fixed. -/
theorem solution
    (χ : SmoothSieveCutoff)
    {k W : ℕ} (hk : 3 ≤ k) (hW : 0 < W)
    (b : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N,
      letI : NeZero N := ⟨hN.ne'⟩
      ∀ n : ZMod N,
        wTrickedPrimeWeight
            (primeScale k χ.normalizer) W b n ≤
          χ.wTrickedMajorant (sieveLevel k N) W b n := by
  have heventually :
      ∀ᶠ N : ℕ in atTop, ∀ hN : 0 < N,
        letI : NeZero N := ⟨hN.ne'⟩
        ∀ n : ZMod N,
          wTrickedPrimeWeight
              (primeScale k χ.normalizer) W b n ≤
            χ.wTrickedMajorant
              (sieveLevel k N) W b n := by
    filter_upwards [
      eventually_ge_atTop (W + b),
      eventually_ge_atTop 1,
      eventually_two_le_sieveLevel hk,
      eventually_sieveLevel_lt_div_sixtyFour hk,
      eventually_sieveExponent_half_mul_log_le_log_sieveLevel hk
    ] with N hWB hNone hRtwo hRbelow hlogLower
    intro hN
    let : NeZero N := ⟨hN.ne'⟩
    exact
      wTrickedPrimeWeight_le_sieveMajorant_of_add_le
        χ hk hNone hW hWB hRtwo hRbelow hlogLower
  exact eventually_atTop.1 heventually
