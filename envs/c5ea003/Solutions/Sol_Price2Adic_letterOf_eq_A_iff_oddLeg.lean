-- Prove2me | solution 1 for Price2Adic.letterOf_eq_A_iff_oddLeg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:40:07.34878+00:00
-- url     : https://prove2.me/submissions/f007a8c3-3fa5-42b1-ae65-cb4275c00d19

-- Sol generated from Cryptography/Price2Adic/Letters.lean
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree
import Theorems.Thm_Price2Adic_oddLeg_mod_four

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






open Price2Adic in
theorem solution(p : ℕ × ℕ) (hp : Valid p) :
    letterOf p = .A ↔ oddLeg p % 4 = 1 := by
  rcases oddLeg_mod_four p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · constructor
    · intro h; exact absurd h h1
    · intro h; omega
