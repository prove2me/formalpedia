-- Prove2me | solution 1 for TropicalSocialChoice.Abstract.semiring_arrow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:03:07.581908+00:00
-- url     : https://prove2.me/submissions/d5e42172-8fee-481f-a240-83221112b15b

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

theorem SForm_apply_single (a : Fin n → S) (j : Fin n) : SForm a (Pi.single j 1) = a j := by
  classical
  rw [SForm, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : (Pi.single j (1 : S) : Fin n → S) b = 0 := Pi.single_eq_of_ne hb 1
    rw [this, mul_zero]
  · intro h; simp at h

@[simp] theorem SForm_zero (a : Fin n → S) : SForm a 0 = 0 := by simp [SForm]






/-- Distinct unit profiles multiply to zero. -/
theorem single_mul_single_eq_zero {j k : Fin n} (hjk : j ≠ k) :
    (Pi.single j (1 : S) : Fin n → S) * (Pi.single k (1 : S) : Fin n → S) = 0 := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    show (Pi.single i (1 : S) : Fin n → S) i * (Pi.single k (1 : S) : Fin n → S) i = 0
    rw [Pi.single_eq_of_ne hjk, mul_zero]
  · show (Pi.single j (1 : S) : Fin n → S) i * (Pi.single k (1 : S) : Fin n → S) i = 0
    rw [Pi.single_eq_of_ne h, zero_mul]

/-- **Key step.**  Multiplicativity makes the coefficients pairwise orthogonal. -/
theorem coeff_mul_coeff_eq_zero {f : (Fin n → S) → S} {a : Fin n → S} (ha : ∀ x, f x = SForm a x)
    (hmul : SScaleInv f) {j k : Fin n} (hjk : j ≠ k) : a j * a k = 0 := by
  have h := hmul (Pi.single j 1) (Pi.single k 1)
  rw [single_mul_single_eq_zero hjk, ha, ha, ha, SForm_zero, SForm_apply_single,
    SForm_apply_single] at h
  exact h.symm

theorem sDictator_injective [Nontrivial S] : Function.Injective (sDictator (S := S) (n := n)) := by
  classical
  intro j k h
  by_contra hjk
  have h1 : (Pi.single j (1 : S) : Fin n → S) j = (Pi.single j (1 : S) : Fin n → S) k :=
    congrFun h (Pi.single j 1)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjk)] at h1
  exact one_ne_zero h1





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
theorem solution[Nontrivial S] [NoZeroDivisors S] {f : (Fin n → S) → S}
    (hlin : IsSLinear f) (hpar : SPareto f) (hmul : SScaleInv f) :
    ∃! k : Fin n, f = sDictator k := by
  classical
  obtain ⟨a, ha⟩ := hlin
  have hex : ∃ k, a k ≠ 0 := by
    by_contra hno
    push_neg at hno
    have h1 : f (fun _ => 1) = 0 := by
      rw [ha, SForm]
      exact Finset.sum_eq_zero fun i _ => by rw [hno i, zero_mul]
    rw [hpar 1] at h1
    exact one_ne_zero h1
  obtain ⟨k, hk⟩ := hex
  have hzero : ∀ j, j ≠ k → a j = 0 := by
    intro j hj
    rcases mul_eq_zero.mp (coeff_mul_coeff_eq_zero ha hmul hj) with h | h
    · exact h
    · exact absurd h hk
  have hfx : ∀ x, f x = a k * x k := by
    intro x
    rw [ha, SForm, Finset.sum_eq_single k]
    · intro b _ hb; rw [hzero b hb, zero_mul]
    · intro h; simp at h
  have hak : a k = 1 := by
    have := hpar 1
    rw [hfx] at this
    simpa using this
  refine ⟨k, ?_, ?_⟩
  · funext x; rw [hfx, hak, one_mul]; rfl
  · intro j hj
    apply sDictator_injective (S := S) (n := n)
    rw [← hj]
    funext x
    rw [hfx, hak, one_mul]; rfl
