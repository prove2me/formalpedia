-- Prove2me | solution 1 for ReciprocityFlipDial.legendre_flip_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:39:01.372902+00:00
-- url     : https://prove2.me/submissions/600c4603-72c7-468e-aba9-323f8888c515

-- Sol generated from Algebra/ReciprocityFlipDial.lean
import Mathlib
import Definitions.Def_Algebra_ReciprocityFlipDial
import Theorems.Thm_ReciprocityFlipDial_twist_eq_pow
/-
# Reciprocity-Flip Dials: the sign artifact behind the paper-226 secondaries

Formal core of experiment **577** (paper 227), diagnostic part (1).

## Background

A *dial* attaches to an integer `N` a vector of quadratic symbols recording, for
each small prime `ℓ`, whether `N` is a quadratic residue mod `ℓ`.  Two
implementations were used in the experimental record:

* the **clean (Legendre) form**  `ℓ ↦ (N | ℓ)`  — symbol with the *prime on the
  bottom*;
* the **product / composite-bottom form** `ℓ ↦ (ℓ | N)` — symbol with the
  *composite* `N` on the bottom, evaluated as a Jacobi symbol.

Experimentally the second form was much weaker as a covariate, and the diagnosis
was that the two forms differ by a **reciprocity sign flip** that switches on
exactly when `ℓ ≡ 3 (mod 4)` and `N ≡ 3 (mod 4)` — reported as "conditional flip
100%, 2680/2680, zero violations".

This file proves that diagnosis, in both the prime-bottom (Legendre) and
composite-bottom (Jacobi) settings, and derives the exact residue bookkeeping
that turns the conditional statement into an unconditional density.

## Main results

* `ReciprocityFlipDial.legendre_flip_of_three_mod_four` — the flip is *total*
  on its condition: for distinct odd primes `p ≡ q ≡ 3 (mod 4)` the two dial
  forms are exact negatives (zero violations).
* `ReciprocityFlipDial.legendre_agree_of_not_both_three_mod_four` — off the
  condition the two forms *agree identically*.
* `ReciprocityFlipDial.legendre_flip_iff` — the sharp dichotomy: the dials flip
  **iff** both primes are `3 mod 4`.
* `ReciprocityFlipDial.jacobi_flip_iff_of_coprime` — the same dichotomy for the
  composite-bottom (Jacobi) dial actually used in the experiment.
* `ReciprocityFlipDial.twist_mul_self`, `ReciprocityFlipDial.jacobi_eq_twist_mul` —
  the flipped form is the clean form multiplied by a `± 1` **twist character**
  depending only on `(ℓ mod 4, N mod 4)`; the twist is an involution, so no
  information is destroyed pointwise, only *linearly* scrambled.
* `ReciprocityFlipDial.twist_sum_eq_zero`, `ReciprocityFlipDial.twist_density` —
  the twist has mean zero over the odd residues mod 4 for a fixed `ℓ ≡ 3 mod 4`,
  and fires on exactly one of the four odd residue pairs (the `25%`
  unconditional rate that the experiment measured after conditioning).
* `ReciprocityFlipDial.dial_twist_scrambles` — a concrete linear-algebra
  consequence: a clean dial that is perfectly correlated with a target can have
  its flipped form *exactly uncorrelated* with the same target.  This is the
  formal content of "the published weakness is a dial-form artifact".
-/

open ReciprocityFlipDial

open Finset

/-! ## 1. The twist character -/







/-! ## 2. The prime-bottom (Legendre) dichotomy -/

variable {p q : ℕ}

/-- **Reciprocity as a dial twist (Legendre form).**  For distinct odd primes,
the composite-bottom symbol `(p | q)` equals the twist times the clean symbol
`(q | p)`. -/
theorem legendre_eq_twist_mul [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p = twist p q * legendreSym p q := by
  have hop : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp
  have hoq : Odd q := (Fact.out : Nat.Prime q).odd_of_ne_two hq
  rw [twist_eq_pow p q hop hoq]
  exact legendreSym.quadratic_reciprocity' hp hq

/-- **Zero violations on the condition.**  If both odd primes are `3 mod 4`
the two dial forms are exact negatives. -/
theorem legendre_flip_of_three_mod_four [Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    (hp : p % 4 = 3) (hq : q % 4 = 3) :
    legendreSym q p = - legendreSym p q := by
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  rw [legendre_eq_twist_mul hp2 hq2, twist, if_pos ⟨hp, hq⟩]
  ring

/-- **Total agreement off the condition.** -/
theorem legendre_agree_of_not_both_three_mod_four [Fact (Nat.Prime p)]
    [Fact (Nat.Prime q)] (hp : p ≠ 2) (hq : q ≠ 2)
    (h : ¬ (p % 4 = 3 ∧ q % 4 = 3)) :
    legendreSym q p = legendreSym p q := by
  rw [legendre_eq_twist_mul hp hq, twist, if_neg h, one_mul]


/-! ## 3. The composite-bottom (Jacobi) dial -/





/-! ## 4. Residue bookkeeping: the unconditional flip density -/




/-! ## 5. The artifact: a twist can annihilate a perfect correlation -/



open ReciprocityFlipDial in
theorem solution[Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    (legendreSym q p = - legendreSym p q) ↔ (p % 4 = 3 ∧ q % 4 = 3) := by
  have hne : legendreSym p q ≠ 0 := by
    rw [Ne, legendreSym.eq_zero_iff]
    have : ¬ ((p : ℤ) ∣ (q : ℤ)) := by
      intro hdvd
      have hdvd' : p ∣ q := by exact_mod_cast hdvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp hdvd')
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast this
  constructor
  · intro hflip
    by_contra hcon
    rw [legendre_agree_of_not_both_three_mod_four hp hq hcon] at hflip
    have : (2 : ℤ) * legendreSym p q = 0 := by linarith
    simp at this
    exact hne this
  · rintro ⟨h1, h2⟩
    exact legendre_flip_of_three_mod_four h1 h2
