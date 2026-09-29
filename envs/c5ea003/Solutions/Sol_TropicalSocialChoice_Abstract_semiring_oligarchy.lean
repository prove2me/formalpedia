-- Prove2me | solution 1 for TropicalSocialChoice.Abstract.semiring_oligarchy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:04:50.994587+00:00
-- url     : https://prove2.me/submissions/94fb1c08-45e6-48f8-b0b0-4c921f905f44

-- Sol generated from Probability/TropicalSocialChoiceSemiring.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceSemiring
import Theorems.Thm_TropicalSocialChoice_Abstract_SForm_eq_sCoalition_of_coeff
import Theorems.Thm_TropicalSocialChoice_Abstract_sSupport_nonempty
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

theorem SForm_apply_single (a : Fin n → S) (j : Fin n) : SForm a (Pi.single j 1) = a j := by
  classical
  rw [SForm, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : (Pi.single j (1 : S) : Fin n → S) b = 0 := Pi.single_eq_of_ne hb 1
    rw [this, mul_zero]
  · intro h; simp at h


theorem SForm_const (a : Fin n → S) (c : S) : SForm a (fun _ => c) = (∑ i, a i) * c := by
  rw [SForm, Finset.sum_mul]

/-- For a linear form, unanimity says exactly that the coefficients sum to `1`. -/
theorem sPareto_SForm_iff (a : Fin n → S) : SPareto (SForm a) ↔ ∑ i, a i = 1 := by
  constructor
  · intro h
    have := h 1
    rwa [SForm_const, mul_one] at this
  · intro h c
    rw [SForm_const, h, one_mul]











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





open TropicalSocialChoice.Abstract in
theorem solution[Nontrivial S] (hidem : ∀ c : S, c * c = c → c = 0 ∨ c = 1)
    {f : (Fin n → S) → S} (hlin : IsSLinear f) (hpar : SPareto f) (hdiag : SDiagIdem f) :
    ∃ s : Finset (Fin n), s.Nonempty ∧ f = sCoalition s := by
  classical
  obtain ⟨a, ha⟩ := hlin
  have hf : f = SForm a := funext ha
  subst hf
  have hsum : ∑ i, a i = 1 := (sPareto_SForm_iff a).mp hpar
  have hsingle : ∀ j : Fin n,
      (Pi.single j (1 : S) : Fin n → S) * Pi.single j 1 = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      show (Pi.single i (1 : S) : Fin n → S) i * (Pi.single i (1 : S) : Fin n → S) i = _
      rw [Pi.single_eq_same, mul_one]
    · show (Pi.single j (1 : S) : Fin n → S) i * (Pi.single j (1 : S) : Fin n → S) i = _
      rw [Pi.single_eq_of_ne hij, mul_zero]
  have hcoeff : ∀ i, a i = 0 ∨ a i = 1 := by
    intro j
    have h1 := hdiag (Pi.single j 1)
    rw [hsingle j, SForm_apply_single] at h1
    exact hidem _ h1.symm
  exact ⟨sSupport a, sSupport_nonempty hcoeff hsum, SForm_eq_sCoalition_of_coeff hcoeff⟩
