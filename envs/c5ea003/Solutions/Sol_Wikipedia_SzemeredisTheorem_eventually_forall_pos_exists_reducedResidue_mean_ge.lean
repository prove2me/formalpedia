-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eventually_forall_pos_exists_reducedResidue_mean_ge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:54:46.649357+00:00
-- url     : https://prove2.me/submissions/5e17ab78-cc3c-4492-ae4f-500d08d3464c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_chebyshev_wTrick_lower_bound
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_log_two_div_four_mul_div_log_le_card
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_reducedResidue_chebyshev_mean_lower_bound
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_wTrickPrimeScale_atTop

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# From primes in a quarter interval to a dense W-tricked prime weight

This file supplies the finite arithmetic bridge in the `W`-trick.  We take
`X = W * (N / 8)`, choose one reduced class among the primes in `(X / 4, X]`,
and send a prime `p` in that class to `(p - b) / W`.  The generous constants
in `greenTaoInterval` make this quotient lie in `[N / 64, N / 4]`.
-/
open Wikipedia.SzemeredisTheorem
open Finset Real Filter
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Uniform-density strengthening of
`eventually_forall_pos_exists_reducedResidue_mean_pos`: the lower bound is
independent of `N`. -/
theorem solution
    {w : ℕ} {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop,
      ∀ hN : 0 < N,
        letI : NeZero N := ⟨hN.ne'⟩
        ∃ b ∈ reducedResidues (primorial w),
          α * log 2 / 128 ≤
            mean
              (wTrickedPrimeWeight α (primorial w) b :
                ZMod N → ℝ) := by
  have hscaleTends :
      Tendsto (wTrickPrimeScale (primorial w)) atTop atTop :=
    tendsto_wTrickPrimeScale_atTop (primorial_pos w)
  have hchebyshev :
      ∀ᶠ N : ℕ in atTop,
        log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N) ≤
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) :=
    hscaleTends.eventually
      eventually_log_two_div_four_mul_div_log_le_card
  have hscaleSixteen :
      ∀ᶠ N : ℕ in atTop,
        16 ≤ wTrickPrimeScale (primorial w) N :=
    hscaleTends.eventually (eventually_ge_atTop 16)
  have hscaleFourW :
      ∀ᶠ N : ℕ in atTop,
        4 * w ≤ wTrickPrimeScale (primorial w) N :=
    hscaleTends.eventually (eventually_ge_atTop (4 * w))
  filter_upwards [
    hchebyshev, hscaleSixteen, hscaleFourW,
    eventually_ge_atTop 16] with
    N hchebyshev hscaleSixteen hscaleFourW hNsixteen
  intro hN
  let : NeZero N := ⟨hN.ne'⟩
  have hw :
      w ≤ wTrickPrimeScale (primorial w) N / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))).2
      (by simpa [Nat.mul_comm] using hscaleFourW)
  obtain ⟨b, hb, hmean⟩ :=
    exists_reducedResidue_chebyshev_mean_lower_bound
      hα.le hw hchebyshev
  refine ⟨b, hb, ?_⟩
  exact
    (chebyshev_wTrick_lower_bound
      (primorial_pos w) hα.le hNsixteen hscaleSixteen).trans hmean
