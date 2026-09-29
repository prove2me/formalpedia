-- Prove2me | solution 1 for ShorIrreducible.exists_factor_of_sqrt_one_zmod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:27:02.051986+00:00
-- url     : https://prove2.me/submissions/7920942f-29c3-4703-aaa1-fba53e350e5c

-- Sol generated from Novelty/ShorOrderFactoring.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Theorems.Thm_ShorIrreducible_exists_factor_of_sqrt_one

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
theorem solution{N : ℕ} (hN : 1 < N) (b : ZMod N)
    (hsq : b ^ 2 = 1) (hne1 : b ≠ 1) (hne2 : b ≠ -1) :
    ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by
  haveI : NeZero N := ⟨by omega⟩
  set x : ℤ := (b.val : ℤ) with hx
  have hcast : ((x : ℤ) : ZMod N) = b := by
    rw [hx]
    push_cast
    exact ZMod.natCast_zmod_val b
  refine exists_factor_of_sqrt_one (x := x) hN ?_ ?_ ?_
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast, hsq, sub_self]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast]
    intro hcon
    exact hne1 (by rwa [sub_eq_zero] at hcon)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast]
    intro hcon
    exact hne2 (by rwa [add_eq_zero_iff_eq_neg] at hcon)
