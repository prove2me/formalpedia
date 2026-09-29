-- Prove2me | Definitions.Def_Bridges_PowerTwoReflectionLatin
-- name    : Bridges_PowerTwoReflectionLatin
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:09.074425+00:00
-- url     : https://prove2.me/theorems/cd797c66-dc4d-4f27-8ace-de3eec639a83
-- title:
--   Aether Catalog definitions — Bridges_PowerTwoReflectionLatin
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PowerTwoReflectionLatin`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PowerTwoReflectionLatin.lean by skeleton subtraction
import Mathlib

/-!
# A bridge: finite 2-groups ↔ powers of two, via pairwise-reflection-symmetric Latin squares

This file formalises the *constructive* half of the conjecture

> a generalized Latin square of order `n` with `λ = 1` possessing **pairwise reflection
> symmetry** exists **iff** `n` is a power of two,

and it proves the exact group–theoretic mechanism that drives it.

## The connection (a cross-domain bridge)

The bridge links three areas:

* **Combinatorics / design theory** — Latin squares and the reflection-symmetry index
  condition on pairs of columns;
* **Group theory** — finite groups of exponent two (every element is an involution),
  i.e. elementary abelian `2`-groups;
* **Number theory** — powers of two.

The key observations, all proved below, are:

1. `cayley_isLatin` : the multiplication (Cayley) table of any finite group is a Latin
   square.
2. `isPRS_cayley_iff_involutive` : that Latin square is **pairwise reflection symmetric
   iff the group has exponent two** (`∀ x, x * x = 1`).  This is the heart of the bridge:
   a purely combinatorial symmetry condition is equivalent to a purely algebraic one.
3. `card_pow_two_of_involutive` : a finite group of exponent two has order a power of two
   (it is a `2`-group).  This is the group-theory ↔ number-theory link.
4. Consequently `card_pow_two_of_cayley_isPRS` : if the Cayley table of `G` is PRS then
   `|G|` is a power of two.
5. `exists_involutive_group_iff_pow_two` : an exponent-two group of order `n` exists **iff**
   `n` is a power of two (the elementary abelian group `(ℤ/2)^k` realises every power).
6. `prs_latin_exists_of_pow_two` : hence for every `k` a pairwise-reflection-symmetric
   Latin square of order `2 ^ k` exists.

The genuinely open direction of the conjecture — that *every* PRS Latin square (not
necessarily a group table) has power-of-two order — is discussed in `FUTURE_DIRECTIONS.md`.
-/

open scoped Classical

namespace PRSLatin

/-! ## Latin squares and pairwise reflection symmetry -/

/-- A square array `L : α → α → α` (rows and columns indexed by the same finite symbol set)
is a **Latin square** if every row and every column is a bijection of the symbol set —
equivalently each symbol occurs exactly once in each row and each column. -/
def IsLatin {α : Type*} (L : α → α → α) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ (∀ j, Function.Bijective fun i => L i j)

/-- The number of rows `i` on which columns `j₁, j₂` read the ordered symbol pair `(p, q)`. -/
noncomputable def pairCount {α : Type*} [Fintype α] (L : α → α → α) (j₁ j₂ p q : α) : ℕ :=
  (Finset.univ.filter fun i => L i j₁ = p ∧ L i j₂ = q).card

/-- **Pairwise reflection symmetry**: on every pair of columns, each ordered symbol pair
`(p, q)` occurs on exactly as many rows as its reversal `(q, p)`. -/
def IsPRS {α : Type*} [Fintype α] (L : α → α → α) : Prop :=
  ∀ j₁ j₂ p q : α, pairCount L j₁ j₂ p q = pairCount L j₁ j₂ q p

/-- A Latin square has **index `λ ≤ 1`** if on every pair of *distinct* columns, no ordered
symbol pair repeats — i.e. reading two columns is injective across rows. -/
def IsIndexLeOne {α : Type*} (L : α → α → α) : Prop :=
  ∀ j₁ j₂ : α, j₁ ≠ j₂ → Function.Injective fun i => (L i j₁, L i j₂)

/-! ## The Cayley table of a group -/

/-- The Cayley (multiplication) table of a type with a multiplication. -/
def cayley (G : Type*) [Mul G] : G → G → G := fun i j => i * j








/-! ## Group theory ↔ number theory: exponent two forces a power of two -/




/-! ## The constructive half of the conjecture -/


end PRSLatin


