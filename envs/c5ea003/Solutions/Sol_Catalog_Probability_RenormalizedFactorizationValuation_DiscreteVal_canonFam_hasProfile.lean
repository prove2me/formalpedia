-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal.canonFam_hasProfile
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T05:20:30.189826+00:00
-- url     : https://prove2.me/submissions/bc1319a6-8420-43bf-b932-2a0c4a6c61d5

-- Sol generated from Speculative/AutoResearch/RenormalizedFactorizationValuation.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
import Theorems.Thm_Catalog_Probability_RenormalizedFactorizationValuation_DiscreteVal_val_uniformizer_zpow
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
theorem solution(k : ℤ) (m : ℕ) (hm : 1 ≤ m) (d : ℕ → ℤ) (g : G)
    (hg : V.val g = k + ∑ i ∈ range m, d i) : HasProfile V m d (canonFam V k m d g) := by
  constructor
  · intro i hi
    by_cases h0 : i = 0
    · subst h0
      have h : canonFam V k m d g 0
          = V.uniformizer ^ (-(k + ∑ j ∈ range m, d j)) * g * V.uniformizer ^ (d 0) := by
        simp [canonFam, hi]
      rw [h, V.val_mul, V.val_mul, V.val_uniformizer_zpow, V.val_uniformizer_zpow, hg]
      ring
    · simp [canonFam, h0, hi]
  · intro i hi
    have h0 : i ≠ 0 := by omega
    have h2 : ¬i < m := by omega
    simp [canonFam, h0, h2]
