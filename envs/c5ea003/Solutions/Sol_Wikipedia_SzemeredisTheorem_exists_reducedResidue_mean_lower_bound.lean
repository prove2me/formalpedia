-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_reducedResidue_mean_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:50:06.180201+00:00
-- url     : https://prove2.me/submissions/20b3b41c-65d9-46cc-b9f7-b91bb7302ef1

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_card_class_mean_lower_bound
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_reducedResidue_card_le_totient_mul_card_fiber

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



namespace Wikipedia.SzemeredisTheorem

open Finset Real
open Filter Asymptotics



@[simp]
theorem mem_primesInQuarterInterval {X p : ℕ} :
    p ∈ primesInQuarterInterval X ↔
      p.Prime ∧ X / 4 < p ∧ p ≤ X := by
  simp [primesInQuarterInterval, and_left_comm, and_comm]





























end Wikipedia.SzemeredisTheorem

end

section





namespace Wikipedia.SzemeredisTheorem

open Finset



@[simp]
theorem mem_reducedResidues {W b : ℕ} :
    b ∈ reducedResidues W ↔ b < W ∧ W.Coprime b := by
  simp [reducedResidues]

















/-- A prime larger than `w` shares no prime factor with the product of
all primes at most `w`. -/
theorem prime_coprime_primorial_of_lt {p w : ℕ} (hp : p.Prime)
    (hw : w < p) :
    p.Coprime (primorial w) := by
  apply hp.coprime_iff_not_dvd.mpr
  rw [hp.dvd_primorial_iff]
  exact not_le.mpr hw



/-- Pigeonhole specialization used in the prime `W`-trick: among any
finite collection of primes larger than `w`, one reduced residue modulo
`primorial w` captures the required proportion. -/
theorem exists_reducedResidue_for_primes_above
    {w : ℕ} (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (habove : ∀ p ∈ S, w < p) :
    ∃ b ∈ reducedResidues (primorial w),
      #S ≤ (primorial w).totient *
        #(residueFiber S (primorial w) b) :=
  exists_reducedResidue_card_le_totient_mul_card_fiber
    (primorial_pos w) S fun p hp ↦
      prime_coprime_primorial_of_lt (hprime p hp) (habove p hp)

end Wikipedia.SzemeredisTheorem

end

section






/-!
# From primes in a quarter interval to a dense W-tricked prime weight

This file supplies the finite arithmetic bridge in the `W`-trick.  We take
`X = W * (N / 8)`, choose one reduced class among the primes in `(X / 4, X]`,
and send a prime `p` in that class to `(p - b) / W`.  The generous constants
in `greenTaoInterval` make this quotient lie in `[N / 64, N / 4]`.
-/

namespace Wikipedia.SzemeredisTheorem

open Finset Real Filter
open scoped BigOperators











































/-- Pigeonhole the quarter-interval primes into reduced residue classes.
The sole size hypothesis says that every sampled prime is larger than `w`. -/
theorem exists_reducedResidue_quarterInterval_card_bound
    {w N : ℕ}
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4) :
    ∃ b ∈ reducedResidues (primorial w),
      #(primesInQuarterInterval
          (wTrickPrimeScale (primorial w) N)) ≤
        (primorial w).totient *
          #(quarterIntervalResidueClass (primorial w) N b) := by
  simpa [quarterIntervalResidueClass] using
    exists_reducedResidue_for_primes_above
      (primesInQuarterInterval
        (wTrickPrimeScale (primorial w) N))
      (fun p hp ↦ (mem_primesInQuarterInterval.mp hp).1)
      (fun p hp ↦ hw.trans_lt
        (mem_primesInQuarterInterval.mp hp).2.1)





























end Wikipedia.SzemeredisTheorem

end
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
/-- Exact Chebyshev-to-mean bridge before inserting the analytic prime-count
bound.  The totient introduced by pigeonholing cancels the totient in the
normalization, leaving only `W` in the denominator. -/
theorem solution
    {w N : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α)
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4) :
    ∃ b ∈ reducedResidues (primorial w),
      (((α / (primorial w : ℝ)) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) ≤
        mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) := by
  obtain ⟨b, hb, hcard⟩ :=
    exists_reducedResidue_quarterInterval_card_bound hw
  refine ⟨b, hb, ?_⟩
  have hcardReal :
      (#(primesInQuarterInterval
          (wTrickPrimeScale (primorial w) N)) : ℝ) ≤
        ((primorial w).totient : ℝ) *
          (#(quarterIntervalResidueClass (primorial w) N b) : ℝ) := by
    exact_mod_cast hcard
  let L : ℝ :=
    log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by
      exact_mod_cast
        (show 1 ≤ wTrickPrimeScale (primorial w) N / 4 + 1 by omega))
  have hscale : 0 ≤ (α / (primorial w : ℝ)) * L :=
    mul_nonneg
      (div_nonneg hα (Nat.cast_nonneg _)) hL
  have hscaled :=
    mul_le_mul_of_nonneg_left hcardReal hscale
  calc
    ((α / (primorial w : ℝ)) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N =
        (((α / (primorial w : ℝ)) * L) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ)) / N := by
      dsimp [L]
      ring
    _ ≤
        (((α / (primorial w : ℝ)) * L) *
          (((primorial w).totient : ℝ) *
            (#(quarterIntervalResidueClass
              (primorial w) N b) : ℝ))) / N := by
      exact div_le_div_of_nonneg_right hscaled (Nat.cast_nonneg N)
    _ =
        (α * (((primorial w).totient : ℝ) / primorial w) *
          ((#(quarterIntervalResidueClass
              (primorial w) N b) : ℝ) *
            log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ))) / N := by
      dsimp [L]
      ring
    _ ≤ mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) :=
      card_class_mean_lower_bound hα (primorial_pos w)
