-- Prove2me | Definitions.Def_Applications_AlienNumberSystems_MixedRadix
-- name    : Applications_AlienNumberSystems_MixedRadix
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:50.472896+00:00
-- url     : https://prove2.me/theorems/8936b4a6-636c-4e99-8cb8-02b676edd1de
-- title:
--   Aether Catalog definitions — Applications_AlienNumberSystems_MixedRadix
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AlienNumberSystems.MixedRadix`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AlienNumberSystems/MixedRadix.lean by skeleton subtraction
import Mathlib

/-!
# Alien Number Systems: the general mixed-radix (variable-base) positional system

`Nat.digits b` formalizes the *uniform* base-`b` positional system: every position
carries the same base `b`.  This file develops the strictly more general
**mixed-radix** (a.k.a. *variable-base* or *alien*) positional system, in which each
position `i` may carry its **own** base `bᵢ`.

The system is specified by a finite list of bases `bs = [b₀, b₁, …, b_{k-1}]`.  A digit
list `ds = [d₀, d₁, …, d_{k-1}]` (least significant first) denotes the value

`mval bs ds = d₀ + b₀·(d₁ + b₁·(d₂ + ⋯))`,

a Horner evaluation.  The digit-extraction map `mdigits bs n` peels off `n % b₀`, then
recurses on `n / b₀` with the remaining bases.

## Main results

* `mval_mdigits` : `mval bs (mdigits bs n) = n % bs.prod` — the master reconstruction law.
* `mval_mdigits_of_lt` : numbers below the *capacity* `bs.prod` round-trip exactly.
* `mdigits_forall₂_lt` : extracted digits are *valid* (`dᵢ < bᵢ`) when every base is positive.
* `mval_lt_prod` : a valid digit list denotes a value `< bs.prod`.
* `mdigits_mval` : valid digit lists round-trip the other way — **uniqueness** of digits.
* `mixedRadixEquiv` : the crowning bijection `Fin bs.prod ≃ {ds // valid digit list}`.

## Specializations ("beyond base-N")

* `MixedRadix.uniformBase` : with `bs = replicate k b` the capacity is `bᵏ`, recovering the
  ordinary uniform base-`b` system as a special case; `mval_replicate_eq_ofDigits` shows the
  alien evaluation literally restricts to Mathlib's `Nat.ofDigits`, and `uniform_roundtrip`
  recovers the classical positional-system theorem.
* `MixedRadix.Factorial` : with `bs = [2, 3, …, k+1]` the capacity is `(k+1)!` and the
  digit bound is `dᵢ ≤ i+1` — the **factorial number system** (factoradic), the canonical
  example of an "alien", genuinely non-uniform, base.

-- !-- Lab Notes -- !--
-- Hypothesis: `Nat.digits` is the uniform shadow of a one-line-more-general object where
--   the per-position base is allowed to vary; existence/uniqueness of representations
--   should be a clean structural induction on the *list of bases* (no well-founded
--   recursion, unlike `Nat.digits`).
-- Experiment: defined `mval`/`mdigits` by structural recursion on the base list and
--   computed factoradic [0,2,0,4] for 100 (= 2·2!+4·4!) and base-10 [3,2,7] for 723.
-- Result: the master law `mval bs (mdigits bs n) = n % bs.prod` reduces, in the inductive
--   step, to exactly `Nat.mod_mul`; everything else (bounds, uniqueness, the bijection)
--   follows from it plus `List.Forall₂`.
-- Insight: the *capacity* of an alien base is the **product** of its digits' bases, the
--   direct generalization of `bᵏ`; the factorial system is the instance `bᵢ = i+2` whose
--   capacity telescopes to `(k+1)!`.
-- Failure analysis: stating digit validity via indexed `dᵢ < bᵢ` is painful; phrasing it
--   as `List.Forall₂ (· < ·) ds bs` makes both round-trips fall out by induction.
-- Iteration 2 (bridge): hypothesized the alien `mval` should *restrict* to Mathlib's
--   `Nat.ofDigits` on uniform bases.  Confirmed by `mval_replicate_eq_ofDigits` (length
--   side-condition `ds.length ≤ k`), establishing the system as a conservative extension
--   of the existing base-N library rather than a parallel reimplementation.
-- !-- End Lab Notes -- !--
-/

namespace MixedRadix

/-- Value of a digit list `ds` in the mixed-radix system with bases `bs`
(least significant first): `d₀ + b₀·(d₁ + b₁·(d₂ + ⋯))`. -/
def mval : List ℕ → List ℕ → ℕ
  | _, [] => 0
  | [], d :: _ => d
  | b :: bs', d :: ds' => d + b * mval bs' ds'

/-- Digit list of `n` in the mixed-radix system with bases `bs` (least significant
first), obtained greedily: `n % b₀ :: mdigits (rest) (n / b₀)`. -/
def mdigits : List ℕ → ℕ → List ℕ
  | [], _ => []
  | b :: bs', n => (n % b) :: mdigits bs' (n / b)




/-
The digit list always has exactly as many entries as there are bases.
-/

/-
**Master reconstruction law.** The value of the extracted digits equals `n` reduced
modulo the system's capacity `bs.prod`.
-/

/-
Numbers below the capacity `bs.prod` are reconstructed exactly.
-/

/-
Extracted digits are **valid**: each is strictly below its position's base,
provided every base is positive.
-/

/-
A valid digit list denotes a value strictly below the capacity.
-/

/-
**Uniqueness of digits.** A valid digit list is recovered exactly by `mdigits`
from the value it denotes.
-/


/-! ### Specialization 1: the ordinary uniform base-`b` system -/

namespace uniformBase

/-
With `k` copies of the base `b`, the capacity is `bᵏ`: the uniform base-`b`
system is the special case of all bases equal.
-/

/-
**Bridge to Mathlib.** On a uniform base list, the mixed-radix evaluation `mval`
agrees with Mathlib's base-`b` evaluation `Nat.ofDigits`, provided the digit list is no
longer than the supply of bases.  Thus the alien system strictly extends `Nat.ofDigits`.
-/

/-
**Uniform round-trip.** A number below `bᵏ` is reconstructed exactly from its
length-`k` uniform base-`b` digits — the classical positional-system theorem recovered
as the uniform instance of the alien framework.
-/

end uniformBase

/-! ### Specialization 2: the factorial number system (factoradic) -/

namespace Factorial

/-- Bases of the factorial number system for numbers below `(k+1)!`:
`[2, 3, …, k+1]`. -/
def bases (k : ℕ) : List ℕ := (List.range k).map (· + 2)

/-
The capacity of the length-`k` factorial system telescopes to `(k+1)!`.
-/

/-
Every factorial base is positive (in fact `≥ 2`).
-/

/-
The factorial system represents exactly `{0, 1, …, (k+1)! - 1}`: numbers below
`(k+1)!` round-trip through their factoradic digits.
-/


end Factorial

end MixedRadix


