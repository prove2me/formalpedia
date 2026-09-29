-- Prove2me | solution 1 for Price2Adic.twoAdic_blind_BC
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:17:05.291776+00:00
-- url     : https://prove2.me/submissions/9fd603fc-c6a8-4726-a6d3-4e0ad46d7ff3

-- Sol generated from Cryptography/Price2Adic/Letters.lean
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree
import Theorems.Thm_Price2Adic_Valid_step
import Theorems.Thm_Price2Adic_letterOf_step

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







/-! ## Position 1: the modulus 8 -/




/-! ## Sharpness: `B` versus `C` is 2-adically invisible -/

theorem oddLeg_eq (m n : ℕ) : Price2Adic.oddLeg (m, n) = m ^ 2 - n ^ 2 := rfl
theorem oddLeg_step_B (p : ℕ × ℕ) (hp : Valid p) :
    oddLeg (step .B p) = oddLeg (step .C p) + 4 * p.1 * p.2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  have h1 : (m - n) ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (m + n) ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  simp only [step, oddLeg_eq]
  zify [h1, h2, hlt.le]
  ring

theorem hyp_step_C (p : ℕ × ℕ) (hp : Valid p) :
    (triple (step .C p)).2.2 = (triple (step .B p)).2.2 + 4 * p.1 * p.2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  simp only [step, triple]
  zify [hlt.le]
  ring

theorem evenLeg_step_C (p : ℕ × ℕ) (hp : Valid p) :
    (triple (step .C p)).2.1 = (triple (step .B p)).2.1 + 8 * p.1 * p.2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  simp only [step, triple]
  zify [hlt.le]
  ring



open Price2Adic in
theorem solution(k : ℕ) :
    ∃ p q : ℕ × ℕ, Valid p ∧ Valid q ∧ letterOf p = .B ∧ letterOf q = .C ∧
      (triple p).1 % 2 ^ k = (triple q).1 % 2 ^ k ∧
      (triple p).2.1 % 2 ^ k = (triple q).2.1 % 2 ^ k ∧
      (triple p).2.2 % 2 ^ k = (triple q).2.2 % 2 ^ k := by
  set r : ℕ × ℕ := (2 ^ k + 1, 2 ^ k) with hr
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
  have hrv : Valid r := by
    refine ⟨by simp [hpos], by simp, ?_, ?_⟩
    · show Nat.gcd (2 ^ k + 1) (2 ^ k) = 1
      simp [Nat.gcd_comm]
    · show (2 ^ k + 1 + 2 ^ k) % 2 = 1
      have : (2 : ℕ) ∣ 2 ^ k + 2 ^ k := ⟨2 ^ k, by ring⟩
      omega
  refine ⟨step .B r, step .C r, Valid_step _ _ hrv, Valid_step _ _ hrv,
    letterOf_step _ _ hrv, letterOf_step _ _ hrv, ?_, ?_, ?_⟩
  · have h := oddLeg_step_B r hrv
    have hd : 4 * r.1 * r.2 = 2 ^ k * (4 * r.1) := by simp only [hr]; ring
    have hA : (triple (step .B r)).1 = oddLeg (step .B r) := by
      obtain ⟨a, b⟩ := step .B r; rfl
    have hC : (triple (step .C r)).1 = oddLeg (step .C r) := by
      obtain ⟨a, b⟩ := step .C r; rfl
    rw [hA, hC, h, hd, Nat.add_mul_mod_self_left]
  · have h := evenLeg_step_C r hrv
    have hd : 8 * r.1 * r.2 = 2 ^ k * (8 * r.1) := by simp only [hr]; ring
    rw [h, hd, Nat.add_mul_mod_self_left]
  · have h := hyp_step_C r hrv
    have hd : 4 * r.1 * r.2 = 2 ^ k * (4 * r.1) := by simp only [hr]; ring
    rw [h, hd, Nat.add_mul_mod_self_left]
