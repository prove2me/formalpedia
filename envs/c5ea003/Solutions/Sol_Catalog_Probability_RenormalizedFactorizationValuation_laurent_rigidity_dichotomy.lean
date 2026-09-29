-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationValuation.laurent_rigidity_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T05:54:39.832128+00:00
-- url     : https://prove2.me/submissions/6d7c7cad-7c5c-4d1b-b282-b64f3ed937b1

-- Sol generated from Speculative/AutoResearch/RenormalizedFactorizationValuation.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
import Theorems.Thm_Catalog_Probability_RenormalizedFactorizationValuation_DiscreteVal_rigidity_dichotomy
/-
# Renormalized factorization over an arbitrary discretely valued group (Cycle 4)

This file closes two of the open conjectures listed in `FUTURE_DIRECTIONS.md` for the
Conjecture-C thread of `Catalog/Probability/RenormalizedNormalizedFactorization.lean`:

* **C4 (transfer to other valued fields).**  Nothing in the Laurent-series proof uses the
  coefficientwise structure of `LaurentSeries K`.  All that is needed is a commutative group
  `G` (the group of units of the field), a homomorphism `val : G → ℤ`, and a uniformizer
  `π` with `val π = 1`.  This is packaged as `DiscreteVal G`.  In this generality:
  `realizable_iff` — for every `m ≥ 1`, every integer exponent `k` and every pole profile
  `d`, the set of `π ^ k * ∏_{i < m} f i` with `val (f i) = d i` is exactly the level set
  `{g | val g = k + ∑_{i<m} d i}`.
* **C1 (rigidity index).**  The fibre of the renormalized-product map over a realizable `g`
  is a torsor under the group of "twists" (`fibreEquivTwist`), and that twist group is in
  bijection with `Fin (m-1)` copies of the valuation-zero subgroup (`twistEquivPi`).  Hence
  `card_factorizations`: the fibre has exactly `#{u | val u = 0} ^ (m-1)` elements — the
  rigidity index is `m - 1`, so the fibre is a singleton **iff** `m = 1`
  (`rigidity_dichotomy`).

The two instantiations proved at the end are genuinely different worlds:

* `laurentVal K` — the Laurent series field `LaurentSeries K` over any field `K`, recovering
  the results of the companion file;
* `padicVal p` — the `p`-adic numbers `ℚ_[p]`, where the same dichotomy is new.

No `sorry`, no `native_decide`, no new axioms.
-/

open Catalog.Probability.RenormalizedFactorizationValuation

open Finset

variable {G : Type*} [CommGroup G]

/-! ## The abstract setting: a `ℤ`-valued valuation with a uniformizer -/


open DiscreteVal

variable (V : DiscreteVal G)








/-! ## Renormalized products and their fibres -/










/-! ## The fibre is a torsor under the twist group -/



/-! ## Rigidity: the fibre is a singleton exactly when `m = 1` -/






/-! ## The rigidity index: the fibre has `#{val = 0} ^ (m-1)` elements -/









/-! ## Instantiation 1: Laurent series -/

open HahnSeries




/-! ## Instantiation 2: the `p`-adic numbers -/

variable (p : ℕ) [hp : Fact p.Prime]





open Catalog.Probability.RenormalizedFactorizationValuation in
theorem solution(K : Type*) [Field K] (k : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (d : ℕ → ℤ) (g : (LaurentSeries K)ˣ)
    (hg : ((g : LaurentSeries K)).order = k + ∑ i ∈ range m, d i) :
    (DiscreteVal.factorizations (laurentVal K) k m d g).Subsingleton ↔ m = 1 := by
  set q : LaurentSeries K := HahnSeries.single (1 : ℤ) (1 : K) with hq
  have hq0 : q ≠ 0 := by simp [hq]
  have hqt : q.orderTop = ((1 : ℤ) : WithTop ℤ) := by
    rw [hq, HahnSeries.orderTop_single (a := (1 : ℤ)) (r := (1 : K)) one_ne_zero]
  have hq1 : (1 : LaurentSeries K).orderTop < q.orderTop := by
    rw [hqt, HahnSeries.orderTop_one]
    exact_mod_cast (by norm_num : ((0 : ℤ) : WithTop ℤ) < ((1 : ℤ) : WithTop ℤ))
  have h2 : (1 + q).orderTop = (0 : WithTop ℤ) := by
    have h := HahnSeries.orderTop_add_eq_left (x := (1 : LaurentSeries K)) (y := q) hq1
    rw [h, HahnSeries.orderTop_one]
  have hone : (1 + q) ≠ 0 := by
    intro h
    rw [h] at h2
    simp at h2
  have hval : (laurentVal K).val (Units.mk0 (1 + q) hone) = 0 := by
    have h3 : (((1 + q).order : ℤ) : WithTop ℤ) = (1 + q).orderTop :=
      HahnSeries.order_eq_orderTop_of_ne_zero hone
    rw [h2] at h3
    show (1 + q).order = 0
    exact_mod_cast h3
  have hne : (Units.mk0 (1 + q) hone) ≠ 1 := by
    intro h
    have h4 : (1 + q) = (1 : LaurentSeries K) := congrArg Units.val h
    exact hq0 (by simpa using h4)
  exact DiscreteVal.rigidity_dichotomy (laurentVal K) k m hm d g hg hval hne
