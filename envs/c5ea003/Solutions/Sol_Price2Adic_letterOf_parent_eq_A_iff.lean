-- Prove2me | solution 1 for Price2Adic.letterOf_parent_eq_A_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:16:18.941036+00:00
-- url     : https://prove2.me/submissions/fb9daa69-0e5f-4794-a8af-90f673b92a9c

-- Sol generated from Cryptography/Price2Adic/Letters.lean
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree
import Theorems.Thm_Price2Adic_letterOf_eq_A_iff

/-!
# The Price alphabet is a 2-adic dial — exactly two letters deep

The Price moves double a parameter, so one expects the address of a node to be readable
from the 2-adic expansion of its triple.  This file makes that precise **and** locates
the exact point where the 2-adic reading stops.

Write `N = oddLeg (m,n) = m² - n²` for the odd leg of the triple of a node, and read a
Price address from the leaf backwards (position `0` = last letter).

* `oddLeg_odd` — `N` is always odd: **the modulus `2` is vacuous**, no information.
* `letter_pos0_iff` — position `0` is `A` **iff** `N ≡ 1 (mod 4)` (and `B`/`C` iff
  `N ≡ 3 (mod 4)`).  A single bit of `N mod 4` determines the last letter.
* `letter_pos1_iff` — position `1` is `A` **iff** `N mod 8 ∈ {1,3}`.  A second bit,
  living in `N mod 8`, determines the previous letter.
* `letter_pos0_pos1_table` — the full `N mod 8` dictionary of the last two letters.
* `twoAdic_blind_BC` — **sharpness**: the `B`/`C` distinction is 2-adically invisible.
  For *every* `k` there are two Price nodes, one a `B`-child and one a `C`-child, whose
  three triple entries agree modulo `2^k`.  Consequently no function of any 2-adic
  residue of the triple can separate `B` from `C`.

So the halving alphabet is a *residue dial of exactly two symbols*: `N mod 8` reads two
letters and nothing more, and the residual ternary choice is invisible at `2`.  This is
the complement of the Berggren picture, whose moves are 3-adic.

## Lab notes (round 70, exp 548)

BFS to depth `8` (`9841` nodes).  For `j = 1, 2` (positions counted from the leaf) the
predicate "letter at position `j` is `A`" is a function of `N mod 2^(j+1)` — a perfect
classifier, and `2^(j+1)` is the smallest such modulus.  For `j = 3, 4, 5` no modulus
`2^k` with `k ≤ 10` classifies: some class always splits.
Tabulated dictionary at `N mod 16` (letters read from the leaf):
`1,9 ↦ AA`, `3,11 ↦ A{B,C}`, `5,13 ↦ {B,C}A`, `7,15 ↦ {B,C}{B,C}`.
`twoAdic_blind_BC` explains the `j ≥ 3` failure at its source: the residual `B`/`C` bit
never enters the 2-adic filtration at all.
-/

open Price2Adic

/-! ## The odd leg -/



/-! ## Position 0: the modulus 4 -/


theorem letterOf_pair_eq_A_iff (m n : ℕ) : letterOf (m, n) = .A ↔ n % 2 = 0 :=
  letterOf_eq_A_iff (m, n)

theorem letterOf_pair_ne_A_iff (m n : ℕ) : letterOf (m, n) ≠ .A ↔ n % 2 = 1 := by
  rw [ne_eq, letterOf_pair_eq_A_iff]
  omega




/-! ## Position 1: the modulus 8 -/




/-! ## Sharpness: `B` versus `C` is 2-adically invisible -/






theorem oddLeg_eq (m n : ℕ) : Price2Adic.oddLeg (m, n) = m ^ 2 - n ^ 2 := rfl
open Price2Adic in
theorem solution(p : ℕ × ℕ) (hp : Valid p) :
    letterOf (parent p) = .A ↔ (oddLeg p % 8 = 1 ∨ oddLeg p % 8 = 3) := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, hpar⟩ := hp
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hlt.le 2
  have key : oddLeg (m, n) + n ^ 2 = m ^ 2 := by simp only [oddLeg_eq]; omega
  rcases Nat.even_or_odd n with hne | hno
  · -- `n` even, `m` odd; parent is `(m - n/2, n/2)`, an `A`-child iff `4 ∣ n`
    obtain ⟨t, ht⟩ := hne
    obtain ⟨s, hs⟩ : ∃ s, m = 2 * s + 1 := ⟨m / 2, by omega⟩
    have hm2 : m ^ 2 = 8 * (s * (s + 1) / 2) + 1 := by
      have hev : 2 ∣ s * (s + 1) := (Nat.even_mul_succ_self s).two_dvd
      obtain ⟨u, hu⟩ := hev
      subst hs
      rw [hu]
      have : (2 * u) / 2 = u := by omega
      rw [this]
      nlinarith [hu]
    have hpar' : parent (m, n) = (m - n / 2, n / 2) := by
      simp only [parent]; rw [if_pos (by omega)]
    rw [hpar', letterOf_eq_A_iff]
    simp only
    rcases Nat.even_or_odd t with hte | hto
    · obtain ⟨r, hr⟩ := hte
      have hn2 : n ^ 2 = 16 * (r * r) := by subst ht; subst hr; ring
      constructor
      · intro _; left; omega
      · intro _; omega
    · obtain ⟨r, hr⟩ := hto
      have hn2 : n ^ 2 = 8 * (2 * (r * r + r)) + 4 := by subst ht; subst hr; ring
      constructor
      · intro h; omega
      · intro h; omega
  · -- `n` odd, `m` even; parent is `(m/2, ·)`, an `A`-child iff `m/2` is odd
    obtain ⟨t, ht⟩ := hno
    obtain ⟨s, hs⟩ : ∃ s, m = 2 * s := ⟨m / 2, by omega⟩
    have hn2 : n ^ 2 = 8 * ((t * (t + 1)) / 2) + 1 := by
      have hev : 2 ∣ t * (t + 1) := (Nat.even_mul_succ_self t).two_dvd
      obtain ⟨u, hu⟩ := hev
      subst ht
      rw [hu]
      have : (2 * u) / 2 = u := by omega
      rw [this]
      nlinarith [hu]
    have hms : m / 2 = s := by omega
    have hpar' : (parent (m, n) = (m / 2, m / 2 - n) ∧ 2 * n < m) ∨
        (parent (m, n) = (m / 2, n - m / 2) ∧ m ≤ 2 * n) := by
      simp only [parent]
      rw [if_neg (by omega)]
      by_cases h : 2 * n < m
      · exact Or.inl ⟨by rw [if_pos h], h⟩
      · exact Or.inr ⟨by rw [if_neg h], by omega⟩
    rcases Nat.even_or_odd s with hse | hso
    · -- `m/2` even: the parent is a `B`/`C`-child and `N ≡ 7 mod 8`
      obtain ⟨r, hr⟩ := hse
      have hm2 : m ^ 2 = 8 * (2 * (r * r)) := by subst hs; subst hr; ring
      have hNval : oddLeg (m, n) % 8 = 7 := by omega
      have : letterOf (parent (m, n)) ≠ .A := by
        rcases hpar' with ⟨h, hbc⟩ | ⟨h, hbc⟩ <;> rw [h, letterOf_pair_ne_A_iff] <;> omega
      constructor
      · intro h; exact absurd h this
      · intro h; omega
    · -- `m/2` odd: the parent is an `A`-child and `N ≡ 3 mod 8`
      obtain ⟨r, hr⟩ := hso
      have hm2 : m ^ 2 = 8 * (2 * (r * r + r)) + 4 := by subst hs; subst hr; ring
      have hNval : oddLeg (m, n) % 8 = 3 := by omega
      have : letterOf (parent (m, n)) = .A := by
        rcases hpar' with ⟨h, hbc⟩ | ⟨h, hbc⟩ <;> rw [h, letterOf_pair_eq_A_iff] <;> omega
      simp [this, hNval]
