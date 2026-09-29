-- Prove2me | Theorems.Thm_Catalog_Probability_RenormalizedFactorizationValuation_laurent_rigidity_dichotomy
-- name    : Catalog.Probability.RenormalizedFactorizationValuation.laurent_rigidity_dichotomy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:37:58.866806+00:00
-- url     : https://prove2.me/theorems/053cbe51-920d-4f8e-bb15-5c391356466f
-- title:
--   Laurent series, rigidity dichotomy.
-- statement:
--   **Laurent series, rigidity dichotomy.**  With the simple-pole profile `d ≡ -1` and `k = m`,
--   the fibre over an order-`0` unit is a singleton iff `m = 1`; the twisting unit `1 + q` provides
--   the nontrivial valuation-zero element over any field.
--
--   ```lean
--   theorem Catalog.Probability.RenormalizedFactorizationValuation.laurent_rigidity_dichotomy(K : Type*) [Field K] (k : ℤ) (m : ℕ) (hm : 1 ≤ m)
--       (d : ℕ → ℤ) (g : (LaurentSeries K)ˣ)
--       (hg : ((g : LaurentSeries K)).order = k + ∑ i ∈ range m, d i) :
--       (DiscreteVal.factorizations (laurentVal K) k m d g).Subsingleton ↔ m = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/RenormalizedFactorizationValuation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/RenormalizedFactorizationValuation.lean#L429

-- Thm stub generated from Speculative/AutoResearch/RenormalizedFactorizationValuation.lean
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

theorem Catalog.Probability.RenormalizedFactorizationValuation.laurent_rigidity_dichotomy(K : Type*) [Field K] (k : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (d : ℕ → ℤ) (g : (LaurentSeries K)ˣ)
    (hg : ((g : LaurentSeries K)).order = k + ∑ i ∈ range m, d i) :
    (DiscreteVal.factorizations (laurentVal K) k m d g).Subsingleton ↔ m = 1 := by sorry
