-- Prove2me | solution 1 for ShorIrreducible.exists_factor_of_sqrt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:25:03.050188+00:00
-- url     : https://prove2.me/submissions/dcde7fed-b634-49a1-a080-f5b993cf252b

-- Sol generated from Novelty/ShorOrderFactoring.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState

/-! # Order finding is factoring: the decisive equivalence, formalized

The assessment of the de-quantization proposal rests on the classical half of
Shor's algorithm: *a sample from the ideal QFT output distribution yields the
order `r`, and the order yields a factor of `N`.*  This file formalizes that
half, and the complementary observation that every regime in which the
tensor-network bond dimension of Shor's state is small is a regime in which the
order is found by classical search.

Main results:

* `exists_factor_of_sqrt_one` : **a nontrivial square root of `1` mod `N`
  produces a nontrivial divisor of `N`** — the classical core of Shor's
  post-processing, via `gcd(x - 1, N)`;
* `exists_factor_of_orderOf_even` : if the order `r` of `a` in `ZMod N` is
  even, positive, and `a^{r/2} ≠ -1`, then `N` has a nontrivial divisor.  So an
  order-finding oracle factors `N`;
* `exists_pow_eq_one_le_of_bondDim` : conversely, if the Shor state admits *any*
  MPS representation of bond dimension `χ` across the register cut, then
  `orderOf a ≤ χ`, hence the order is exhibited by a search of length `χ`: a
  polynomial bond dimension is a polynomial-time classical order-finding
  algorithm.  Low rank and classical easiness coincide.
-/

open Finset

open ShorIrreducible

/-! ## A nontrivial square root of one factors `N` -/




/-- The reduction is not vacuous: `4` is a nontrivial square root of `1`
modulo `15`, and `gcd(4 - 1, 15) = 3`. -/
example : ((4 : ZMod 15) ^ 2 = 1 ∧ (4 : ZMod 15) ≠ 1 ∧ (4 : ZMod 15) ≠ -1) ∧
    Int.gcd ((4 : ℤ) - 1) (15 : ℤ) = 3 := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide⟩

/-! ## Low bond dimension means a classically easy order -/

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]




open ShorIrreducible in
theorem solution{N : ℕ} (hN : 1 < N) {x : ℤ}
    (hsq : (N : ℤ) ∣ x ^ 2 - 1) (hne1 : ¬ (N : ℤ) ∣ x - 1) (hne2 : ¬ (N : ℤ) ∣ x + 1) :
    ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  classical
  set d : ℕ := Int.gcd (x - 1) (N : ℤ) with hd
  have hdvdN : (d : ℕ) ∣ N := by
    have : (d : ℤ) ∣ (N : ℤ) := Int.gcd_dvd_right _ _
    exact_mod_cast this
  have hd1 : d ≠ 1 := by
    intro h1
    have hcop : IsCoprime (x - 1) (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr h1
    have hfac : (N : ℤ) ∣ (x - 1) * (x + 1) := by
      have : (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      rw [this]
      exact hsq
    exact hne2 (hcop.symm.dvd_of_dvd_mul_left hfac)
  have hdN : d ≠ N := by
    intro hDN
    apply hne1
    have : (d : ℤ) ∣ (x - 1) := Int.gcd_dvd_left _ _
    rwa [hDN] at this
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · exfalso
      have : (N : ℕ) = 0 := Nat.eq_zero_of_zero_dvd (h0 ▸ hdvdN)
      omega
    · exact h
  refine ⟨d, hdvdN, ?_, ?_⟩
  · omega
  · exact lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvdN) hdN
