-- Prove2me | solution 1 for PRSLatin.isPRS_cayley_iff_involutive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:25:38.970737+00:00
-- url     : https://prove2.me/submissions/1f22ee17-6686-494e-a2fe-f6af4c5a8684

-- Sol generated from Bridges/PowerTwoReflectionLatin.lean
import Mathlib
import Definitions.Def_Bridges_PowerTwoReflectionLatin
import Theorems.Thm_PRSLatin_cayley_pairCount

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









/-! ## Group theory ↔ number theory: exponent two forces a power of two -/




/-! ## The constructive half of the conjecture -/



open PRSLatin in
theorem solution(G : Type*) [Group G] [Fintype G] :
    IsPRS (cayley G) ↔ ∀ x : G, x * x = 1 := by
  constructor
  · intro hPRS x
    have h := hPRS 1 x 1 x
    rw [cayley_pairCount, cayley_pairCount] at h
    -- first `if` is true (condition `x = x`), forcing the second to be `1` too
    simp only [inv_one, one_mul, mul_one, if_true] at h
    by_contra hx
    rw [if_neg hx] at h
    exact one_ne_zero h
  · intro hinv j₁ j₂ p q
    rw [cayley_pairCount, cayley_pairCount]
    -- Set `w = j₁⁻¹ * j₂`; then `w * w = 1`, so `p * w = q ↔ q * w = p`.
    set w := j₁⁻¹ * j₂ with hw
    have hww : w * w = 1 := hinv w
    have e1 : p * j₁⁻¹ * j₂ = p * w := by rw [hw, mul_assoc]
    have e2 : q * j₁⁻¹ * j₂ = q * w := by rw [hw, mul_assoc]
    rw [e1, e2]
    congr 1
    apply propext
    constructor
    · intro h; rw [← h, mul_assoc, hww, mul_one]
    · intro h; rw [← h, mul_assoc, hww, mul_one]
