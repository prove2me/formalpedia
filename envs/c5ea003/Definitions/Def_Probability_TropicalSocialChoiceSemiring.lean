-- Prove2me | Definitions.Def_Probability_TropicalSocialChoiceSemiring
-- name    : Probability_TropicalSocialChoiceSemiring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:22.420328+00:00
-- url     : https://prove2.me/theorems/85c3e946-0393-4a46-9880-bbee1714d906
-- title:
--   Aether Catalog definitions — Probability_TropicalSocialChoiceSemiring
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TropicalSocialChoiceSemiring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TropicalSocialChoiceSemiring.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
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

namespace TropicalSocialChoice

/-! ## The abstract theory over a commutative semiring -/

namespace Abstract

open Finset

variable {S : Type*} [CommSemiring S] {n : ℕ}

/-- The linear form with coefficient vector `a`: `x ↦ ⨁ᵢ aᵢ ⊙ xᵢ`.  Over `S = TR` this is
`TropicalSocialChoice.tropForm`. -/
def SForm (a x : Fin n → S) : S := ∑ i, a i * x i

/-- `f` is a semiring-linear map (a `1 × n` matrix over `S`). -/
def IsSLinear (f : (Fin n → S) → S) : Prop := ∃ a : Fin n → S, ∀ x, f x = SForm a x

/-- Unanimity. -/
def SPareto (f : (Fin n → S) → S) : Prop := ∀ c : S, f (fun _ => c) = c

/-- Additivity (the abstract form of tropical IIA). -/
def SIIA (f : (Fin n → S) → S) : Prop := ∀ x y, f (x + y) = f x + f y

/-- Multiplicativity (the abstract form of tropical scale invariance). -/
def SScaleInv (f : (Fin n → S) → S) : Prop := ∀ x y, f (x * y) = f x * f y

/-- Diagonal idempotence: multiplicativity restricted to the diagonal. -/
def SDiagIdem (f : (Fin n → S) → S) : Prop := ∀ x, f (x * x) = f x * f x

/-- The dictator: society copies voter `k`. -/
def sDictator (k : Fin n) : (Fin n → S) → S := fun x => x k

/-- `f` is dictatorial. -/
def IsSDictatorial (f : (Fin n → S) → S) : Prop := ∃ k, f = sDictator k

/-- The coalition rule of `s`: `x ↦ ⨁_{i ∈ s} xᵢ`. -/
def sCoalition (s : Finset (Fin n)) : (Fin n → S) → S := fun x => ∑ i ∈ s, x i

open scoped Classical in
/-- The support (oligarchy) of a coefficient vector: the voters entering with weight `1`. -/
noncomputable def sSupport (a : Fin n → S) : Finset (Fin n) :=
  Finset.univ.filter fun i => a i = 1


/-! ### Elementary lemmas -/















/-! ### The abstract Arrow theorem -/




/-! ### The abstract oligarchy theorem -/




end Abstract

/-! ## The min-plus semiring is the special case `S = TR` -/

section Tropical

open Abstract

variable {n : ℕ}








end Tropical

/-! ## Conjecture 5, first half: any linearly ordered cancellative monoid of costs -/

section GeneralTropical

open Abstract Tropical

variable {G : Type*} [LinearOrder G] [AddCancelCommMonoid G] [IsOrderedAddMonoid G] {n : ℕ}

instance : Nontrivial (Tropical (WithTop G)) :=
  ⟨⟨0, 1, fun h => by
      have := congrArg untrop h
      exact (WithTop.coe_ne_top (a := (0 : G))) (by simpa using this.symm)⟩⟩




end GeneralTropical

/-! ## Conjecture 5, second half: the bounded min–max semiring -/

/-- The **bounded min–max semiring** on a type `α`: tropical addition is `⊓` (with unit
`⊤`, the tropical zero) and tropical multiplication is `⊔` (with unit `⊥`, the tropical
one).  Unlike min-plus, this semiring is *not* cancellative — its multiplication is
idempotent. -/
def MinMax (α : Type*) : Type _ := α

namespace MinMax

variable {α : Type*}

instance [LinearOrder α] : LinearOrder (MinMax α) := inferInstanceAs (LinearOrder α)

instance [LinearOrder α] [BoundedOrder α] : BoundedOrder (MinMax α) :=
  inferInstanceAs (BoundedOrder α)

instance [Nontrivial α] : Nontrivial (MinMax α) := inferInstanceAs (Nontrivial α)

instance [LinearOrder α] [BoundedOrder α] : CommSemiring (MinMax α) where
  add a b := a ⊓ b
  zero := (⊤ : MinMax α)
  mul a b := a ⊔ b
  one := (⊥ : MinMax α)
  nsmul k a := if k = 0 then (⊤ : MinMax α) else a
  nsmul_zero _ := rfl
  nsmul_succ k a := by
    cases k with
    | zero => exact (top_inf_eq a).symm
    | succ m => exact (inf_idem a).symm
  add_assoc a b c := inf_assoc a b c
  zero_add a := top_inf_eq a
  add_zero a := inf_top_eq a
  add_comm a b := inf_comm a b
  mul_assoc a b c := sup_assoc a b c
  one_mul a := bot_sup_eq a
  mul_one a := sup_bot_eq a
  mul_comm a b := sup_comm a b
  left_distrib a b c := sup_inf_left a b c
  right_distrib a b c := sup_inf_right a b c
  zero_mul a := top_sup_eq a
  mul_zero a := sup_top_eq a

variable [LinearOrder α] [BoundedOrder α]

theorem mul_def (a b : MinMax α) : a * b = a ⊔ b := rfl
theorem zero_def : (0 : MinMax α) = ⊤ := rfl

/-- The min–max semiring on a *linear* order has no zero divisors: `a ⊔ b = ⊤` forces
`a = ⊤` or `b = ⊤`. -/
instance : NoZeroDivisors (MinMax α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    rw [mul_def, zero_def] at h
    rcases le_total a b with hab | hab
    · right; rw [zero_def, ← h, sup_eq_right.mpr hab]
    · left; rw [zero_def, ← h, sup_eq_left.mpr hab]


end MinMax

section MinMaxArrow

open Abstract

variable {α : Type*} [LinearOrder α] [BoundedOrder α] [Nontrivial α] {n : ℕ}





end MinMaxArrow

/-! ## Sharpness: zero divisors really do allow non-dictatorial rules -/

section ZeroDivisors

open Abstract

variable {R R' : Type*} [CommSemiring R] [CommSemiring R'] [Nontrivial R] [Nontrivial R']



end ZeroDivisors

end TropicalSocialChoice


