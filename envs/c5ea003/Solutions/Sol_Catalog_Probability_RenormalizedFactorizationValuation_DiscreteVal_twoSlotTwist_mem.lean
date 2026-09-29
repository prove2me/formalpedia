-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal.twoSlotTwist_mem
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T05:29:13.152801+00:00
-- url     : https://prove2.me/submissions/a18d9ada-6492-48c6-bd8b-6baf6bb43252

-- Sol generated from Speculative/AutoResearch/RenormalizedFactorizationValuation.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
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
theorem solution(m : ℕ) (hm : 2 ≤ m) {u : G} (hu : V.val u = 0) :
    twoSlotTwist u ∈ twistGroup V m := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    by_cases h0 : i = 0
    · simp [twoSlotTwist, h0, hu]
    · by_cases h1 : i = 1 <;> simp [twoSlotTwist, h0, h1, hu]
  · intro i hi
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    simp [twoSlotTwist, h0, h1]
  · have hsub : range 2 ⊆ range m := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have h1 : ∏ i ∈ range 2, twoSlotTwist u i = ∏ i ∈ range m, twoSlotTwist u i := by
      refine Finset.prod_subset hsub ?_
      intro x _ hx
      have h0 : x ≠ 0 := by
        intro h; exact hx (by simp [h])
      have h1 : x ≠ 1 := by
        intro h; exact hx (by simp [h])
      simp [twoSlotTwist, h0, h1]
    rw [← h1]
    simp [twoSlotTwist, Finset.prod_range_succ]
