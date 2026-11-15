-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.dvd_iff_primePower_dvd
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:50:16.165733+00:00
-- url     : https://prove2.me/submissions/d22792d2-3e4d-4134-ac6f-960ab747128d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# CRT factorization of paired divisibility densities

The divisor expansion of a product of Selberg weights leaves an exact finite
density `pairedDivisibilityDensity`.  This file isolates the arithmetic steps
which can be performed without any analytic estimate.

First, the two divisor conditions attached to one form are replaced by their
least common multiple.  The resulting zero--one function is identified with
the indicator of its exact finite support, and each nonzero local modulus is
then decomposed into its prime-power divisibility conditions.

Second, normalized means are reindexed by the Chinese remainder theorem.
For any finite pairwise-coprime family of moduli, a product of functions which
depends separately on the corresponding CRT components has mean equal to the
product of its local means.  We specialize this both to two moduli and to the
canonical prime-power decomposition of a nonzero modulus.

For arbitrary natural-valued forms, CRT factorization is not automatic: one
must still show that the global paired divisibility indicator depends on the
CRT components as a product of local indicators.  The final definitions and
theorems package precisely that remaining obligation, without asserting a
false independence statement.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Collapsing paired divisibility conditions -/
/-! ## Prime-power divisibility data -/

open Wikipedia.SzemeredisTheorem in
/-- Divisibility by a nonzero integer is equivalent to divisibility by every
prime power in its canonical factorization. -/
theorem solution
    {d n : ℕ} (hd : d ≠ 0) :
    d ∣ n ↔
      ∀ p : d.primeFactors,
        (p : ℕ) ^ d.factorization p ∣ n := by
  constructor
  · intro h p
    have hp :
        (p : ℕ) ^ d.factorization p ∣
          ∏ q : d.primeFactors,
            (q : ℕ) ^ d.factorization q :=
      Finset.dvd_prod_of_mem
      (fun q : d.primeFactors =>
        (q : ℕ) ^ d.factorization q)
      (Finset.mem_univ p)
    rw [← Nat.prod_pow_primeFactors_factorization hd] at hp
    exact hp.trans h
  · intro h
    have hlcm :
        Finset.univ.lcm
            (fun p : d.primeFactors =>
              (p : ℕ) ^ d.factorization p) ∣ n :=
      Finset.lcm_dvd fun p _hp => h p
    have hpair :
        Set.Pairwise (Finset.univ : Finset d.primeFactors)
          (Nat.Coprime.onFun fun p : d.primeFactors =>
            (p : ℕ) ^ d.factorization p) :=
      d.pairwise_coprime_pow_primeFactors_factorization.set_pairwise _
    rw [Finset.lcm_eq_prod hpair] at hlcm
    rw [← Nat.prod_pow_primeFactors_factorization hd] at hlcm
    exact hlcm
