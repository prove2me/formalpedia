-- Prove2me | Theorems.Thm_PRSLatin_isPRS_cayley_iff_involutive
-- name    : PRSLatin.isPRS_cayley_iff_involutive
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:01:15.412971+00:00
-- url     : https://prove2.me/theorems/c8fa5885-37af-4b6a-8baf-5796c019c74d
-- title:
--   Heart of the bridge.
-- statement:
--   **Heart of the bridge.** The Cayley table of a finite group is pairwise reflection
--   symmetric **iff** the group has exponent two. A combinatorial symmetry ⟺ an algebraic one.
--
--   ```lean
--   theorem PRSLatin.isPRS_cayley_iff_involutive(G : Type*) [Group G] [Fintype G] :
--       IsPRS (cayley G) ↔ ∀ x : G, x * x = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PowerTwoReflectionLatin.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PowerTwoReflectionLatin.lean#L130

-- Thm stub generated from Bridges/PowerTwoReflectionLatin.lean
import Mathlib
import Definitions.Def_Bridges_PowerTwoReflectionLatin

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

open PRSLatin

/-! ## Latin squares and pairwise reflection symmetry -/





/-! ## The Cayley table of a group -/

theorem PRSLatin.isPRS_cayley_iff_involutive(G : Type*) [Group G] [Fintype G] :
    IsPRS (cayley G) ↔ ∀ x : G, x * x = 1 := by sorry
