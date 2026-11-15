-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:27.617277+00:00
-- url     : https://prove2.me/submissions/1506a407-4bc0-47c1-a9bc-de3ad0c09d1d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section






/-!
# Smooth truncated divisor sums

The Goldston--Yıldırım majorant is the square of a smoothly truncated
Möbius divisor sum.  This file fixes the normalization and proves the exact
prime-value identity used for pointwise domination of the W-tricked prime
weight.  The later linear-forms estimate is deliberately separated from
these elementary identities.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators







/-- On a prime, only the divisors `1` and `p` occur.  If the cutoff vanishes
at the prime endpoint, the divisor sum is exactly its `d = 1` term. -/
theorem smoothTruncatedDivisorSum_prime
    (χ : ℝ → ℝ) (R : ℕ) {p : ℕ}
    (hp : p.Prime)
    (hcut : χ (Real.log p / Real.log R) = 0) :
    smoothTruncatedDivisorSum χ R p =
      Real.log R * χ 0 := by
  unfold smoothTruncatedDivisorSum
  rw [hp.divisors]
  apply congrArg (fun t : ℝ => Real.log R * t)
  have h1p : 1 ∉ ({p} : Finset ℕ) := by
    simpa using hp.ne_one.symm
  rw [Finset.sum_insert h1p, Finset.sum_singleton, hcut]
  simp

/-- With the standard normalization `χ 0 = 1`, the truncated divisor sum
equals `log R` on primes beyond the cutoff. -/
theorem smoothTruncatedDivisorSum_prime_of_chi_zero
    (χ : ℝ → ℝ) (R : ℕ) {p : ℕ}
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hcut : χ (Real.log p / Real.log R) = 0) :
    smoothTruncatedDivisorSum χ R p = Real.log R := by
  rw [smoothTruncatedDivisorSum_prime χ R hp hcut, hχ0, mul_one]

/-- A cutoff supported below one vanishes at `log p / log R` whenever
`R < p`. -/
theorem smoothCutoff_zero_of_lt
    (χ : ℝ → ℝ) {R p : ℕ}
    (hR : 1 < R) (hRp : R < p)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0) :
    χ (Real.log p / Real.log R) = 0 := by
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  apply hχ
  rw [le_div_iff₀ hlogR]
  simpa using
    (Real.log_lt_log
      (by exact_mod_cast (Nat.zero_lt_of_lt hR))
      (by exact_mod_cast hRp)).le





/-- Prime-value identity in the form used later: support of `χ` and
`R < p` discharge the endpoint hypothesis automatically. -/
theorem smoothTruncatedDivisorSum_prime_of_lt
    (χ : ℝ → ℝ) {R p : ℕ}
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hR : 1 < R) (hRp : R < p) :
    smoothTruncatedDivisorSum χ R p = Real.log R :=
  smoothTruncatedDivisorSum_prime_of_chi_zero χ R hp hχ0
    (smoothCutoff_zero_of_lt χ hR hRp hχ)



theorem smoothSelbergWeight_nonneg
    (χ : ℝ → ℝ) (R n : ℕ) :
    0 ≤ smoothSelbergWeight χ R n :=
  sq_nonneg _







theorem smoothSelbergWeight_prime_of_lt
    (χ : ℝ → ℝ) {R p : ℕ}
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hR : 1 < R) (hRp : R < p) :
    smoothSelbergWeight χ R p = Real.log R ^ 2 := by
  rw [smoothSelbergWeight,
    smoothTruncatedDivisorSum_prime_of_lt χ hp hχ0 hχ hR hRp]



theorem normalizedSelbergMajorant_nonneg
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : 0 ≤ cχ)
    {R : ℕ} (hR : 1 ≤ R) (W n : ℕ) :
    0 ≤ normalizedSelbergMajorant χ cχ R W n := by
  unfold normalizedSelbergMajorant
  have hlogR : 0 ≤ Real.log (R : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hR)
  exact div_nonneg
    (mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (smoothSelbergWeight_nonneg χ R n))
    (mul_nonneg hcχ hlogR)

/-- Exact normalized value on a prime beyond the cutoff. -/
theorem normalizedSelbergMajorant_prime_of_lt
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : cχ ≠ 0)
    {R W p : ℕ} (hR : 1 < R) (hW : 0 < W)
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hRp : R < p) :
    normalizedSelbergMajorant χ cχ R W p =
      (W.totient : ℝ) / W * (Real.log R / cχ) := by
  unfold normalizedSelbergMajorant
  rw [smoothSelbergWeight_prime_of_lt χ hp hχ0 hχ hR hRp]
  have hlogR : Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  have hW0 : (W : ℝ) ≠ 0 := by
    exact_mod_cast hW.ne'
  field_simp [hcχ, hlogR, hW0]

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























/-- Pointwise domination reduced to its only substantive case: a prime
inside the short interval. -/
theorem wTrickedPrimeWeight_le_majorant_of_prime_bound
    {N : ℕ} [NeZero N]
    (α : ℝ) (W b : ℕ)
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : 0 ≤ cχ)
    {R : ℕ} (hR : 1 ≤ R)
    (hprime :
      ∀ n : ZMod N,
        n.val ∈ greenTaoInterval N →
        Nat.Prime (wTrickedValue W b n) →
        α * ((W.totient : ℝ) / W) *
            Real.log (wTrickedValue W b n) ≤
          normalizedSelbergMajorant χ cχ R W
            (wTrickedValue W b n)) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight α W b n ≤
        wTrickedMajorant χ cχ R W b n := by
  intro n
  by_cases hn : n.val ∈ greenTaoInterval N
  · by_cases hp : Nat.Prime (wTrickedValue W b n)
    · simpa [wTrickedPrimeWeight, wTrickedMajorant, hn, hp] using
        hprime n hn hp
    · simp [wTrickedPrimeWeight, wTrickedMajorant, hn, hp,
        normalizedSelbergMajorant_nonneg χ hcχ hR W
          (wTrickedValue W b n)]
  · simp [wTrickedPrimeWeight, wTrickedMajorant, hn]



end Wikipedia.SzemeredisTheorem

end
/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- The exact prime-value identity for the Selberg square turns a scalar
logarithmic comparison into pointwise domination. -/
theorem solution
    {N : ℕ} [NeZero N]
    {α cχ : ℝ} (hcχ : 0 < cχ)
    {R W b : ℕ} (hR : 1 < R) (hW : 0 < W)
    (χ : ℝ → ℝ) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hscale :
      ∀ n : ZMod N,
        n.val ∈ greenTaoInterval N →
        Nat.Prime (wTrickedValue W b n) →
        R < wTrickedValue W b n ∧
          α * Real.log (wTrickedValue W b n) ≤
            Real.log R / cχ) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight α W b n ≤
        wTrickedMajorant χ cχ R W b n := by
  apply wTrickedPrimeWeight_le_majorant_of_prime_bound
    α W b χ hcχ.le hR.le
  intro n hn hp
  rw [normalizedSelbergMajorant_prime_of_lt χ hcχ.ne'
    hR hW hp hχ0 hχ (hscale n hn hp).1]
  calc
    α * ((W.totient : ℝ) / W) *
          Real.log (wTrickedValue W b n) =
        ((W.totient : ℝ) / W) *
          (α * Real.log (wTrickedValue W b n)) := by ring
    _ ≤ ((W.totient : ℝ) / W) * (Real.log R / cχ) :=
      mul_le_mul_of_nonneg_left (hscale n hn hp).2
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
