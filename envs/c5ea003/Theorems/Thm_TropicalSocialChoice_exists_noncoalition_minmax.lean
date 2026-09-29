-- Prove2me | Theorems.Thm_TropicalSocialChoice_exists_noncoalition_minmax
-- name    : TropicalSocialChoice.exists_noncoalition_minmax
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:15:55.70242+00:00
-- url     : https://prove2.me/theorems/2e1ee0b8-84d4-4633-8450-1ddbb3922d1f
-- title:
--   A witness that the min–max oligarchy statement genuinely fails: if `α` has an element
-- statement:
--   A witness that the min–max oligarchy statement genuinely fails: if `α` has an element
--   strictly between `⊥` and `⊤`, there is a linear, unanimous, diagonally idempotent rule on
--   two voters which is **not** a coalition rule.  (By `minmax_arrow` it is of course not
--   multiplicative either.)
--
--   ```lean
--   theorem TropicalSocialChoice.exists_noncoalition_minmax{c : MinMax α} (hb : ⊥ < c) (ht : c < ⊤) :
--       ∃ f : (Fin 2 → MinMax α) → MinMax α,
--         IsSLinear f ∧ SPareto f ∧ SDiagIdem f ∧ ∀ s : Finset (Fin 2), f ≠ sCoalition s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TropicalSocialChoiceSemiring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TropicalSocialChoiceSemiring.lean#L496

-- Thm stub generated from Probability/TropicalSocialChoiceSemiring.lean
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




omit [Nontrivial α] in

theorem TropicalSocialChoice.exists_noncoalition_minmax{c : MinMax α} (hb : ⊥ < c) (ht : c < ⊤) :
    ∃ f : (Fin 2 → MinMax α) → MinMax α,
      IsSLinear f ∧ SPareto f ∧ SDiagIdem f ∧ ∀ s : Finset (Fin 2), f ≠ sCoalition s := by sorry
