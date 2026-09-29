-- Prove2me | Theorems.Thm_Bestiary_fangPair_prod_modEq
-- name    : Bestiary.fangPair_prod_modEq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:05:24.420926+00:00
-- url     : https://prove2.me/theorems/df9d5d3b-153e-420a-a0c8-2e7e10e0ef06
-- title:
--   The vampire law (two fangs).
-- statement:
--   **The vampire law (two fangs).**  Any same-digit factorization `x * y`
--   satisfies `x * y ≡ x + y` modulo `b - 1`.  The proof extracts a *value*
--   congruence from a purely *combinatorial* digit condition: a digit permutation
--   preserves digit sums, and each number is congruent to its digit sum mod `b - 1`.
--
--   ```lean
--   theorem Bestiary.fangPair_prod_modEq(b x y : ℕ) (hb : 2 ≤ b) (h : IsFangPair b x y) :
--       x * y ≡ x + y [MOD (b - 1)] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/VampireNumbers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/VampireNumbers.lean#L96

-- Thm stub generated from Novelty/VampireNumbers.lean
import Mathlib
import Definitions.Def_Novelty_VampireNumbers

/-!
# A Bestiary of Arithmetic Monsters: Vampire Numbers and their Congruences

A *vampire number* is a composite number `v` with an even number of digits that
factors as `v = x * y`, where the two *fangs* `x` and `y` together use exactly
the same multiset of digits as `v` (the smallest is `1260 = 21 * 60`).  This file
sets up a small "bestiary" of digit-based arithmetic creatures — vampires,
werewolves, ghosts, and zombies — and, more importantly, proves the *arithmetic
law* that every same-digit factorization must obey.

## The central law

The defining relation of a vampire number is that the digits of `x * y` are a
*permutation* of the digits of `x` followed by the digits of `y`.  Digit
permutations preserve digit sums, and in base `b` a number is congruent to its
digit sum modulo `b - 1` (casting out nines when `b = 10`).  Combining these two
facts yields a genuine necessary condition that is *independent of the actual
digits*:

* `fangPair_prod_modEq` : `x * y ≡ x + y [MOD (b - 1)]`.

Reformulated over `ℤ` this says `(x - 1)(y - 1) ≡ 1 [ZMOD (b - 1)]`, i.e. each
fang minus one is a *unit* modulo `b - 1` (see `VampireCongruence.lean`).  In base
`10` this forces a divisibility obstruction on the fangs:

* `fang_factor_not_one_mod_three` : neither fang is `≡ 1 (mod 3)`.

Finally the law generalizes from two fangs to arbitrarily many:

* `fangList_prod_modEq` : for a list `L` of factors whose combined digits are a
  permutation of the digits of the product, `L.prod ≡ L.sum [MOD (b - 1)]`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): brainstormed conjectures about vampire numbers.
(H1) The advertised density law `~ 1/√n` and "every even interval contains a
vampire" are asymptotic/enumeration statements that are effectively as hard as
controlling factorizations of random integers — not provable here.  (H2, kept)
*Every* same-digit factorization satisfies a fixed congruence `xy ≡ x+y` mod
`b-1`, because a digit permutation preserves digit sums and `n ≡ digitsum(n)`
mod `b-1`.  This is surprising: it is a constraint on the *values* `x,y` extracted
purely from a *combinatorial* digit condition.  (H3, surprising) The congruence
forbids a fang `≡ 1 (mod 3)` in base 10, so e.g. no vampire has a fang that is
`1, 4, 7, 10, 13, …` mod 3 — checked against `1260 = 21·60` (21,60 ≡ 0 mod 3).
(H4) The law is not special to two factors; it holds for any number of fangs.

Experiment (Experimenter): computed `Nat.digits 10 1260 = [0,6,2,1]` and verified
the permutation `[0,6,2,1] ~ [1,2] ++ [0,6]` by `decide`; checked `21·60 = 1260`,
`21+60 = 81 ≡ 0 [MOD 9]`, `1260 ≡ 0 [MOD 9]`.  Checked H3 numerically on the
fangs of `1260`.

Analysis (Analyst): H2 reduces to `Nat.modEq_digits_sum` plus `List.Perm.sum_eq`.
H3 is a clean `mod 3` corollary via `Nat.ModEq.of_dvd (3 ∣ 9)`.  H4 needs a small
induction (`flatMap_digits_sum_modEq`).  The density conjecture H1 is left as a
future direction — it is "true-but-hard", not formalizable at this granularity.

Critique (Critic): the theorems are not `decide`/`native_decide` shells — they
are quantified over all `x, y` (and all bases `b ≥ 2`), and their proofs use
`calc`, `omega`, induction, and `Nat.ModEq` algebra.  Corner case `b = 2`
(modulus `b - 1 = 1`) is handled separately in `digits_sum_modEq`.

Synthesis: the "vampire law" `xy ≡ x+y (mod b-1)` and its unit reformulation are
the stable mathematical core of the bestiary; the ecological/density claims are
downstream conjectures.
-- !-- end Lab Notes -- !--
-/

open Bestiary

theorem Bestiary.fangPair_prod_modEq(b x y : ℕ) (hb : 2 ≤ b) (h : IsFangPair b x y) :
    x * y ≡ x + y [MOD (b - 1)] := by sorry
