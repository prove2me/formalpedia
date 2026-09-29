-- Prove2me | Definitions.Def_MachineLearning_CASpacetimeAperiodicity
-- name    : MachineLearning_CASpacetimeAperiodicity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:37:54.02787+00:00
-- url     : https://prove2.me/theorems/d0186365-2ff9-4e64-97f5-aee1f47e6193
-- title:
--   Aether Catalog definitions — MachineLearning_CASpacetimeAperiodicity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CASpacetimeAperiodicity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CASpacetimeAperiodicity.lean by skeleton subtraction
import Mathlib

/-!
# Aperiodicity of CA Spacetime Column Language Transition Monoids

## Main results

* `RightPermutative.existsUnique_right`: A right-permutative binary operation
  has unique solutions for its right argument.

* `partialConst_iterate_three_eq_two`: Any partial constant function with
  absorbing zero satisfies `f³ = f²`. This is the aperiodicity condition
  with uniform exponent 2.

* The transition monoid of any CA spacetime column language is aperiodic,
  implying the language is star-free by Schützenberger's theorem.

## Key insight

The spacetime column language of a nearest-neighbor CA is a "graph path language":
a word `σ₁σ₂...σₖ` over the alphabet of columns is accepted iff consecutive
columns are pairwise compatible under the CA rule. The DFA for this language
has a special structure where each transition function is a "partial constant
function" — it maps a subset of states to a single target and sends everything
else to a dead/absorbing state.

For such functions, squaring either yields the same function (if the target is
in the source set) or the zero function (if not). In either case, `m³ = m²`.
This gives aperiodicity with uniform exponent bound 2.
-/

open Function

/-! ## Part 1: Right-Permutative Operations -/

/-- A binary operation `f : α → α → α` is right-permutative if for each fixed
left argument `a`, the map `b ↦ f a b` is a bijection. -/
def RightPermutative {α : Type*} (f : α → α → α) : Prop :=
  ∀ a : α, Bijective (f a)




/-! ## Part 2: Spacetime Column Compatibility -/

/-- Two columns `c₁, c₂ : Fin h → α` are compatible under a nearest-neighbor
CA rule `f` if applying `f` row-by-row with `c₂` as the right neighbor
produces the next time step encoded in `c₁`. -/
def SpacetimeCompatible {α : Type*} (f : α → α → α) {h : ℕ}
    (c₁ c₂ : Fin h → α) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < h),
    c₁ ⟨i + 1, hi⟩ = f (c₁ ⟨i, by omega⟩) (c₂ ⟨i, by omega⟩)


/-! ## Part 3: Partial Constant Functions and Aperiodicity -/

/-- A function `f : Option α → Option α` is a "partial constant function"
if it maps `none` to `none` (absorbing state) and maps every `some a` to either
a fixed `some c` or to `none`. -/
structure IsPartialConst {α : Type*} (f : Option α → Option α) : Prop where
  none_fixed : f none = none
  target_exists : ∃ c : α, ∀ a : α, f (some a) = some c ∨ f (some a) = none


/-
**Key Lemma**: Any partial constant function satisfies `f ∘ f ∘ f = f ∘ f`.
This is the aperiodicity condition with uniform exponent 2.

Proof sketch: Let `c` be the target of `f`.
- Case 1: `f(some c) = some c`. Then `f` is idempotent on its range
  (`f² = f`), so `f³ = f²`.
- Case 2: `f(some c) = none`. Then `f²` maps everything to `none`
  (since `f` maps to either `some c` or `none`, and `f(some c) = none`,
  `f(none) = none`). So `f² = const none`, and `f³ = f²`.
-/

/-
Corollary: `f ∘ f` is idempotent for partial constant functions.
-/

/-! ## Part 4: Monoid Aperiodicity -/

/-- A monoid is aperiodic if every element has some power that is idempotent. -/
def IsAperiodicMonoid (M : Type*) [Monoid M] : Prop :=
  ∀ m : M, ∃ k : ℕ, m ^ (k + 1) = m ^ k

/-
Quotients of aperiodic monoids are aperiodic. This connects the transition
monoid of any DFA to the syntactic monoid of the recognized language.
-/


