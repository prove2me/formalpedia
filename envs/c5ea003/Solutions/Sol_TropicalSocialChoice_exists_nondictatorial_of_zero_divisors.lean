-- Prove2me | solution 1 for TropicalSocialChoice.exists_nondictatorial_of_zero_divisors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:58:35.161323+00:00
-- url     : https://prove2.me/submissions/5525e3b3-a274-4de1-9c59-df237ed4bf4f

-- Sol generated from Probability/TropicalSocialChoiceSemiring.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceSemiring
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice III: how much of the base semiring does Arrow's theorem use?

`Probability.TropicalSocialChoice` proved the *tropical Arrow theorem* in the min-plus
semiring `TR = Tropical (WithTop ℝ)`: tropical IIA (`f (x ⊕ y) = f x ⊕ f y`), tropical
Pareto (`f (c,…,c) = c`) and tropical multiplicativity (`f (x ⊙ y) = f x ⊙ f y`) force
`f` to be a projection.  `Probability.TropicalSocialChoiceOligarchy` weakened
multiplicativity to diagonal idempotence and obtained the coalition (oligarchy) rules.

Conjecture 5 of `FUTURE_DIRECTIONS.md` asked how much of this depends on the particular
semiring `TR`.  This file answers it completely, and the answer is sharper than
conjectured.

## Main results

* `semiring_arrow`, `semiring_arrow_of_sIIA`, `semiring_arrow_iff` : **the tropical Arrow
  theorem is a theorem about arbitrary nontrivial commutative semirings without zero
  divisors.**  For such a semiring `S`, the maps `f : Sⁿ → S` that are additive,
  multiplicative and unanimous are exactly the coordinate projections, and the projecting
  coordinate is unique.  Additivity + multiplicativity + unanimity already give linearity
  (`isSLinear_of_sIIA`), exactly as in the min-plus case.
* `tropical_arrow_of_semiring_arrow` : the original min-plus theorem is the special case
  `S = TR`, so nothing was lost in the abstraction.
* `tropical_arrow_general` : the first half of Conjecture 5, proved — the theorem holds
  over `Tropical (WithTop G)` for *every* linearly ordered cancellative additive
  commutative monoid `G` (in particular every linearly ordered abelian group), because
  such a semiring is nontrivial and has no zero divisors.
* `semiring_oligarchy`, `tropical_oligarchy_general` : the oligarchy theorem likewise
  holds over any semiring whose multiplicative idempotents are only `0` and `1`, which is
  automatic for `Tropical (WithTop G)` with `G` cancellative.
* `MinMax`, `minmax_arrow` : the second half of Conjecture 5 is **refuted**.  The bounded
  min–max semiring `(α, ⊕ = ⊓, ⊙ = ⊔)` on a bounded linear order — which is *not*
  cancellative, its multiplication being idempotent — nevertheless has no zero divisors,
  so its unanimous additive multiplicative rules are again exactly the dictators.  Thus
  the tropical Arrow theorem is a statement about zero-divisor-freeness, not about
  cancellativity.
* `minmax_sDiagIdem_all`, `exists_noncoalition_minmax` : cancellativity *is* what the
  oligarchy theorem needs.  Over `MinMax α` every rule is diagonally idempotent, and if
  `α` has an element strictly between `⊥` and `⊤` there is a unanimous linear diagonally
  idempotent rule on two voters that is not a coalition rule.
* `exists_nondictatorial_of_zero_divisors` : zero-divisor-freeness cannot be dropped
  either.  In a product semiring `R × R'` the rule
  `x ↦ (1,0) ⊙ x₀ ⊕ (0,1) ⊙ x₁` is linear, unanimous and multiplicative but not a
  dictatorship.

Together: over a nontrivial commutative semiring, *dictatorship ⟺ no zero divisors* is the
exact dividing line for the tropical Arrow axioms.
-/

open TropicalSocialChoice

/-! ## The abstract theory over a commutative semiring -/

open Abstract

open Finset

variable {S : Type*} [CommSemiring S] {n : ℕ}












/-! ### Elementary lemmas -/















/-! ### The abstract Arrow theorem -/




/-! ### The abstract oligarchy theorem -/





/-! ## The min-plus semiring is the special case `S = TR` -/


open Abstract

variable {n : ℕ}









/-! ## Conjecture 5, first half: any linearly ordered cancellative monoid of costs -/


open Abstract Tropical

variable {G : Type*} [LinearOrder G] [AddCancelCommMonoid G] [IsOrderedAddMonoid G] {n : ℕ}






/-! ## Conjecture 5, second half: the bounded min–max semiring -/


open MinMax

variable {α : Type*}



instance [Nontrivial α] : Nontrivial (MinMax α) := inferInstanceAs (Nontrivial α)


variable [LinearOrder α] [BoundedOrder α]






open Abstract

variable {α : Type*} [LinearOrder α] [BoundedOrder α] [Nontrivial α] {n : ℕ}






/-! ## Sharpness: zero divisors really do allow non-dictatorial rules -/


open Abstract

variable {R R' : Type*} [CommSemiring R] [CommSemiring R'] [Nontrivial R] [Nontrivial R']

omit [Nontrivial R] [Nontrivial R'] in
/-- The two-voter rule over the product semiring picking the first component from voter `0`
and the second from voter `1`. -/
theorem prodSplit_apply (x : Fin 2 → R × R') :
    SForm ![((1 : R), (0 : R')), ((0 : R), (1 : R'))] x = ((x 0).1, (x 1).2) := by
  rw [SForm, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp




open TropicalSocialChoice in
theorem solution:
    ∃ f : (Fin 2 → R × R') → R × R',
      IsSLinear f ∧ SPareto f ∧ SIIA f ∧ SScaleInv f ∧ ¬ IsSDictatorial f := by
  classical
  set a : Fin 2 → R × R' := ![((1 : R), (0 : R')), ((0 : R), (1 : R'))] with ha
  have happ : ∀ x : Fin 2 → R × R', SForm a x = ((x 0).1, (x 1).2) := fun x => prodSplit_apply x
  refine ⟨SForm a, ⟨a, fun _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [happ]
  · intro x y
    rw [happ, happ, happ]
    ext <;> simp
  · intro x y
    rw [happ, happ, happ]
    ext <;> simp
  · rintro ⟨k, hk⟩
    have h0 : SForm a ![((1 : R), (1 : R')), ((0 : R), (0 : R'))] = ((1 : R), (0 : R')) := by
      rw [happ]; rfl
    have h1 : sDictator k ![((1 : R), (1 : R')), ((0 : R), (0 : R'))]
        = ![((1 : R), (1 : R')), ((0 : R), (0 : R'))] k := rfl
    rw [hk, h1] at h0
    fin_cases k
    · exact zero_ne_one (congrArg Prod.snd h0).symm
    · exact zero_ne_one (congrArg Prod.fst h0)
