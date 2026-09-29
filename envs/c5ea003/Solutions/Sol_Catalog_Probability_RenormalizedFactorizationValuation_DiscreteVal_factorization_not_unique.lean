-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal.factorization_not_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T05:36:55.290655+00:00
-- url     : https://prove2.me/submissions/c8d77ea7-d30c-4a13-a6f2-d434fb076e5d

-- Sol generated from Speculative/AutoResearch/RenormalizedFactorizationValuation.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
import Theorems.Thm_Catalog_Probability_RenormalizedFactorizationValuation_DiscreteVal_twoSlotTwist_mem
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





open Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal in
theorem solution(k : ℤ) (m : ℕ) (hm : 2 ≤ m) (d : ℕ → ℤ) (g : G)
    {u : G} (hu : V.val u = 0) (hu1 : u ≠ 1)
    {f : ℕ → G} (hf : f ∈ factorizations V k m d g) :
    ∃ f' ∈ factorizations V k m d g, f' ≠ f := by
  have hm1 : 1 ≤ m := by omega
  set e := V.fibreEquivTwist k m d g f hf with he
  refine ⟨(e.symm ⟨twoSlotTwist u, V.twoSlotTwist_mem m hm hu⟩ : ℕ → G),
    (e.symm ⟨twoSlotTwist u, V.twoSlotTwist_mem m hm hu⟩).2, ?_⟩
  intro hcontra
  have h0 : f 0 * u = f 0 := by
    have : (e.symm ⟨twoSlotTwist u, V.twoSlotTwist_mem m hm hu⟩ : ℕ → G) 0 = f 0 * u := by
      simp [he, fibreEquivTwist, twoSlotTwist]
    rw [← this, hcontra]
  have h1 : f 0 * u = f 0 * 1 := by rw [mul_one]; exact h0
  exact hu1 (mul_left_cancel h1)
