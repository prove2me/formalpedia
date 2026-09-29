-- Prove2me | solution 1 for Bestiary.fangPair_int_congr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:47:55.939006+00:00
-- url     : https://prove2.me/submissions/45455719-8167-4ea3-8aae-d1cd21d05973

-- Sol generated from Novelty/VampireCongruence.lean
import Mathlib
import Definitions.Def_Novelty_VampireNumbers
import Theorems.Thm_Bestiary_fangPair_prod_modEq

/-!
# The Unit Reformulation of the Vampire Law

Building on `Novelty.VampireNumbers`, this file records the *integer* face of the
vampire law.  The base-`b` law `x * y ≡ x + y [MOD (b - 1)]` (proved as
`Bestiary.fangPair_prod_modEq`) is, over `ℤ`, equivalent to

`(x - 1) * (y - 1) ≡ 1 [ZMOD (b - 1)]`,

i.e. *each fang, decremented by one, is a unit modulo `b - 1`.*  This is the sharp
algebraic obstruction that makes vampire (and werewolf/zombie) numbers scarce:
the pair `(x - 1, y - 1)` must be a pair of mutually-inverse residues.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the additive congruence `xy ≡ x+y` should have a
cleaner multiplicative shadow.  Since `(x-1)(y-1) = xy - x - y + 1`, the law is
exactly `(x-1)(y-1) ≡ 1`.  Conjecture: this is the *only* residue obstruction —
every residue pair with `(x-1)(y-1) ≡ 1 (mod b-1)` is realized by some genuine
fang pair (left as a future direction).

Experiment (Experimenter): `1260 = 21·60`, `(21-1)(60-1) = 20·59 = 1180`, and
`1180 mod 9 = 1`.  ✓.  Base 12: `(x-1)(y-1) ≡ 1 (mod 11)`.

Analysis (Analyst): the proof needs the `ℕ → ℤ` transfer of `Nat.ModEq`
(`exact_mod_cast`), the cast identity `↑(b-1) = ↑b - 1` for `b ≥ 1`, and a `ring`
rearrangement.  The only subtlety is truncated `ℕ`-subtraction inside the modulus,
handled by `Nat.cast_sub`.

Critique (Critic): not a definitional `rfl` — the statement mixes `ℤ`
multiplication with a congruence transported from `ℕ`, and the proof genuinely
uses `Int.ModEq` algebra (`sub_right`, `add_right`) plus `ring`.  The hypothesis
`2 ≤ b` is load-bearing (it makes `↑(b-1) = ↑b - 1`).

Synthesis: the unit reformulation upgrades the additive vampire law to a
multiplicative unit condition, tying the digit combinatorics to the group of
units modulo `b - 1`.
-- !-- end Lab Notes -- !--
-/

open Bestiary




open Bestiary in
theorem solution(b x y : ℕ) (hb : 2 ≤ b) (h : IsFangPair b x y) :
    ((x : ℤ) - 1) * ((y : ℤ) - 1) ≡ 1 [ZMOD ((b : ℤ) - 1)] := by
  have hn : x * y ≡ x + y [MOD (b - 1)] := fangPair_prod_modEq b x y hb h
  have hz : ((x * y : ℕ) : ℤ) ≡ ((x + y : ℕ) : ℤ) [ZMOD ((b - 1 : ℕ) : ℤ)] := by
    exact_mod_cast hn
  have hbcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    have h1 : (1 : ℕ) ≤ b := by omega
    push_cast [Nat.cast_sub h1]; ring
  rw [hbcast] at hz
  have hz' : (x : ℤ) * (y : ℤ) ≡ (x : ℤ) + (y : ℤ) [ZMOD ((b : ℤ) - 1)] := by
    push_cast at hz; exact hz
  calc ((x : ℤ) - 1) * ((y : ℤ) - 1)
      = (x : ℤ) * (y : ℤ) - ((x : ℤ) + (y : ℤ)) + 1 := by ring
    _ ≡ ((x : ℤ) + (y : ℤ)) - ((x : ℤ) + (y : ℤ)) + 1 [ZMOD ((b : ℤ) - 1)] :=
        ((hz'.sub_right _).add_right _)
    _ = 1 := by ring
