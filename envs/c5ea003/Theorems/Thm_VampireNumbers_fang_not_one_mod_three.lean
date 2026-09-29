-- Prove2me | Theorems.Thm_VampireNumbers_fang_not_one_mod_three
-- name    : VampireNumbers.fang_not_one_mod_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:07:22.902546+00:00
-- url     : https://prove2.me/theorems/e4e9642b-9a51-4ff4-af7a-a88e4c3cbc56
-- title:
--   The mod-3 unit obstruction.
-- statement:
--   **The mod-3 unit obstruction.**  In any digit-permutation factorization,
--   *neither fang is congruent to `1` modulo `3`*.  Indeed if `x ≡ 1 (mod 3)` then
--   `x*y ≡ x+y (mod 3)` collapses to `y ≡ 1 + y`, i.e. `0 ≡ 1 (mod 3)`.
--
--   *Analysis:* casting the mod-3 identity into `ZMod 3` turns the obstruction into
--   a two-element linear contradiction.
--
--   ```lean
--   theorem VampireNumbers.fang_not_one_mod_three{x y : ℕ} (h : DigitPermFactorization x y) :
--       x % 3 ≠ 1 ∧ y % 3 ≠ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Combinatorics/VampireNumbers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Combinatorics/VampireNumbers.lean#L106

-- Thm stub generated from Applications/Combinatorics/VampireNumbers.lean
import Mathlib
import Definitions.Def_Applications_Combinatorics_VampireNumbers

/-!
# Vampire Numbers and the Arithmetic of Digit-Permutation Factorizations

A *vampire number* is a composite number `v` with an even number of (base-10)
digits admitting a factorization `v = x * y`, where `x` and `y` (the *fangs*)
each have half as many digits as `v` and **together use exactly the multiset of
digits of `v`**, subject to the classical side condition that `x` and `y` do not
both end in `0`.  The smallest example is `1260 = 21 · 60`.

The heart of the definition is a purely combinatorial constraint: the digits of
`x` and `y`, taken together, are a permutation of the digits of the product
`x * y`.  We isolate this as `DigitPermFactorization` and derive three
structural obstructions that every such factorization must satisfy.  These are
the arithmetic "silver bullets" that any candidate vampire pair must survive.

## Main results

* `VampireNumbers.castingOutNines` — **casting out nines for factorizations**:
  a digit-permutation factorization forces `x * y ≡ x + y [MOD 9]`,
  equivalently `(x-1)(y-1) ≡ 1 [MOD 9]`.
* `VampireNumbers.fang_not_one_mod_three` — a sharp corollary: neither fang can
  be `≡ 1 (mod 3)`.  This is a genuine sieve that eliminates candidate pairs.
* `VampireNumbers.digit_length_additive` — a digit-permutation factorization
  forces the product to have the *maximal* possible length
  `len(x*y) = len(x) + len(y)`, i.e. the multiplication loses no leading digit.

We then package the classical definition (`IsVampirePair` / `IsVampire`) and
verify `1260 = 21 · 60` as an honest instance, showing the three obstructions in
action.

-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer):  We floated several conjectures.
  (H1) The stated density claim "vampire numbers have density → 1/√n in
       [10^{2n},10^{2n+1}]" is ill-posed: 1/√n → 0, so it asserts vanishing
       density, contradicting the intended reading of "density approaches 1".
       We flag it as false-as-stated and do not pursue it.
  (H2, SURVIVED) Casting out nines must constrain any digit-permutation
       factorization: since a number is ≡ its digit sum (mod 9) and the fang
       digits are a permutation of the product's digits, `x*y ≡ x+y (mod 9)`.
  (H3, SURVIVED, SURPRISING) The mod-9 identity `(x-1)(y-1) ≡ 1 (mod 9)` forces
       both `x-1` and `y-1` to be units mod 3, hence *no fang is ≡ 1 (mod 3)* —
       a one-line sieve rejecting ~1/3 of candidate factors.
  (H4, SURVIVED) The permutation condition forbids "carry shrinkage": the
       product must have length exactly len(x)+len(y).

Experiment (Experimenter):  Base cases confirm H2/H3/H4: for 1260 = 21·60,
  21·60 = 1260 ≡ 21+60 = 81 ≡ 0 (mod 9); 21 ≡ 0, 60 ≡ 0 (mod 3), neither ≡ 1;
  len(1260)=4 = len(21)+len(60)=2+2.  Mathlib supplies
  `Nat.modEq_nine_digits_sum` (`n ≡ (digits 10 n).sum [MOD 9]`), which is the
  exact fuel for H2.

Analysis (Analyst):  See sibling `Analysis` blocks; H2–H4 are all true and
  proved.  H1 is false as literally stated.  The multiset formulation (rather
  than `List.Perm`) is what makes the sum/length transfers a one-line
  `congrArg`.

Critique (Critic):  None of the three main theorems is `decide`/`native_decide`;
  each transports a Mathlib modular/multiset lemma through the permutation
  hypothesis.  The `1260` instance uses `decide` only for the concrete finite
  digit computation, not for a universally-quantified claim.

Synthesis (PI):  Casting out nines + the mod-3 unit obstruction + length
  additivity form a compact, reusable "bestiary sieve" for arithmetic monsters.
-/

open VampireNumbers

open Nat

theorem VampireNumbers.fang_not_one_mod_three{x y : ℕ} (h : DigitPermFactorization x y) :
    x % 3 ≠ 1 ∧ y % 3 ≠ 1 := by sorry
