-- Prove2me | solution 1 for PRSLatin.prs_latin_exists_of_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:27:28.224857+00:00
-- url     : https://prove2.me/submissions/a6f26dc5-e98b-4d99-acf1-d05695b2d486

-- Sol generated from Bridges/PowerTwoReflectionLatin.lean
import Mathlib
import Definitions.Def_Bridges_PowerTwoReflectionLatin
import Theorems.Thm_PRSLatin_isPRS_cayley_iff_involutive

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



/-- The Cayley table of a group is a Latin square. -/
theorem cayley_isLatin (G : Type*) [Group G] : IsLatin (cayley G) := by
  constructor
  · intro i; exact Group.mulLeft_bijective i
  · intro j; exact Group.mulRight_bijective j

/-- The Cayley table of a group has index `≤ 1`: the value in two columns determines the
row. -/
theorem cayley_isIndexLeOne (G : Type*) [Group G] : IsIndexLeOne (cayley G) := by
  intro j₁ j₂ _ a b h
  have : a * j₁ = b * j₁ := (Prod.mk.injEq .. ▸ h).1
  exact mul_right_cancel this





/-! ## Group theory ↔ number theory: exponent two forces a power of two -/




/-! ## The constructive half of the conjecture -/



open PRSLatin in
theorem solution(k : ℕ) :
    ∃ (α : Type) (_ : Fintype α) (L : α → α → α),
      Nat.card α = 2 ^ k ∧ IsLatin L ∧ IsPRS L ∧ IsIndexLeOne L := by
  refine ⟨Multiplicative (Fin k → ZMod 2), inferInstance, cayley _, ?_, ?_, ?_, ?_⟩
  · simp [Nat.card_eq_fintype_card]
  · exact cayley_isLatin _
  · refine (isPRS_cayley_iff_involutive _).mpr ?_
    intro x
    induction x using Multiplicative.rec with
    | _ a =>
      rw [← ofAdd_add]
      simp only [← ofAdd_zero]
      congr 1
      ext i
      exact CharTwo.add_self_eq_zero _
  · exact cayley_isIndexLeOne _
