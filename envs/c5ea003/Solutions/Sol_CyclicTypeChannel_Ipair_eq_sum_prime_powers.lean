-- Prove2me | solution 1 for CyclicTypeChannel.Ipair_eq_sum_prime_powers
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:32:25.617185+00:00
-- url     : https://prove2.me/submissions/861a2d9e-08f6-44b9-a51a-4b53aec23452

-- Sol generated from Shared/CyclicTypeChannelCRTLaw.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
import Theorems.Thm_CyclicTypeChannel_Ipair_mul_of_coprime
import Theorems.Thm_CyclicTypeChannel_uEnt_of_card_le_one
/-
# The CRT additivity law for the splitting-type channel

The exact evaluations show an arithmetic law behind the numbers: for coprime
cyclic orders the type-pair channel is *additive*,

  `I_pair (m * n) = I_pair m + I_pair n`.

This file proves the law in general (for the ordered type pair) from three
ingredients:

* the Chinese Remainder Theorem, which relabels the sample set `box (m*n)` as
  the product `box m ×ˢ box n`;
* the multiplicativity of the splitting type,
  `ord_{mn}(a) = ord_m(a) · ord_n(a)`, together with the fact that this
  factorisation is an *injective recoding* of the pair of component types;
* the additivity of the counting channel over independent products
  (`mutInfo_prod`).

The consequence is a structural explanation of the growth table:
the information of a cyclic order is a sum of primary contributions, so the
one-bit binary cap can be exceeded simply by multiplying orders together.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. The ordered type-pair channel -/




/-! ## 2. Multiplicativity of the splitting type -/



/-! ## 3. The CRT relabelling of the sample set -/





/-! ## 4. The additivity law -/


/-! ## 5. From the ordered to the unordered pair -/




/-! ## 6. The channel is determined by its prime-power values -/

/-- The trivial cyclic order carries no information. -/
theorem Ipair_one : Ipair 1 = 0 := by
  have hcard : (box 1).card ≤ 1 := by decide
  have hcond : condEnt (box 1) (typePair 1) (prodRes 1) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have : (#{x ∈ box 1 | prodRes 1 x = c}) ≤ 1 :=
      le_trans (Finset.card_filter_le _ _) hcard
    rw [uEnt_of_card_le_one this, mul_zero]
  rw [Ipair, mutInfo, uEnt_of_card_le_one hcard, hcond, sub_zero]



open CyclicTypeChannel in
theorem solution{n : ℕ} (hn : n ≠ 0) :
    Ipair n = ∑ p ∈ n.primeFactors, Ipair (p ^ n.factorization p) := by
  have hmul : ∀ (a b : ℕ), Nat.Coprime a b →
      Real.exp (Ipair (a * b)) = Real.exp (Ipair a) * Real.exp (Ipair b) := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [Nat.coprime_zero_left] at hab
      subst hab
      simp [Ipair_one]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp only [Nat.coprime_zero_right] at hab
      subst hab
      simp [Ipair_one]
    rw [Ipair_mul_of_coprime ha hb hab, Real.exp_add]
  have hone : Real.exp (Ipair 1) = 1 := by rw [Ipair_one, Real.exp_zero]
  have hfac := Nat.multiplicative_factorization (fun m => Real.exp (Ipair m)) hmul hone hn
  rw [Finsupp.prod, Nat.support_factorization] at hfac
  simp only at hfac
  have hsum : ∏ p ∈ n.primeFactors, Real.exp (Ipair (p ^ n.factorization p))
      = Real.exp (∑ p ∈ n.primeFactors, Ipair (p ^ n.factorization p)) :=
    (Real.exp_sum _ _).symm
  rw [hsum] at hfac
  exact Real.exp_injective hfac
