-- Prove2me | Definitions.Def_Novelty_VampireNumbers
-- name    : Novelty_VampireNumbers
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:50:14.463524+00:00
-- url     : https://prove2.me/theorems/5c7c715b-178a-43d8-a28d-31e7abe2f082
-- title:
--   Aether Catalog definitions — Novelty_VampireNumbers
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.VampireNumbers`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/VampireNumbers.lean by skeleton subtraction
import Mathlib

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

namespace Bestiary

/-- The **fang relation** in base `b`: the digits of the product `x * y` are a
permutation of the digits of `x` together with the digits of `y`.  This is the
defining combinatorial condition behind vampire numbers. -/
def IsFangPair (b x y : ℕ) : Prop :=
  (Nat.digits b (x * y)).Perm (Nat.digits b x ++ Nat.digits b y)

/-- The multi-factor generalization of the fang relation: the digits of the
product `L.prod` are a permutation of all the digits of all factors in `L`. -/
def IsFangList (b : ℕ) (L : List ℕ) : Prop :=
  (Nat.digits b L.prod).Perm (L.flatMap (Nat.digits b))







/-! ### The rest of the bestiary (faithful definitions)

These record the other "creatures" from the mission statement.  The main
theorems above apply to any `IsFangPair`/`IsFangList`; the definitions below are
kept for downstream enumeration and future work. -/






/-! ### Concrete inhabitants (sanity checks, not main results) -/

end Bestiary


