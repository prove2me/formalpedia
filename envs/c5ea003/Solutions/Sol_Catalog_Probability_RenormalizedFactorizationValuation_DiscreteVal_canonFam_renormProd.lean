-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationValuation.DiscreteVal.canonFam_renormProd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T05:29:12.593367+00:00
-- url     : https://prove2.me/submissions/d0815ca7-e436-41e5-a3a9-d1bfbc2baaa8

-- Sol generated from Speculative/AutoResearch/RenormalizedFactorizationValuation.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationValuation
import Theorems.Thm_Catalog_Probability_RenormalizedFactorizationValuation_DiscreteVal_prod_uniformizer_zpow
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
theorem solution(k : ℤ) (m : ℕ) (hm : 1 ≤ m) (d : ℕ → ℤ) (g : G) :
    renormProd V k m (canonFam V k m d g) = g := by
  have h1 : ∏ i ∈ range m, canonFam V k m d g i
      = (∏ i ∈ range m, (if i = 0 then V.uniformizer ^ (-(k + ∑ j ∈ range m, d j)) * g else 1))
        * ∏ i ∈ range m, (if i < m then V.uniformizer ^ (d i) else 1) := by
    simp only [canonFam]
    rw [← Finset.prod_mul_distrib]
  have h2 : (∏ i ∈ range m, (if i = 0 then V.uniformizer ^ (-(k + ∑ j ∈ range m, d j)) * g else 1))
      = V.uniformizer ^ (-(k + ∑ j ∈ range m, d j)) * g := by
    rw [Finset.prod_eq_single 0]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg hb]
    · intro h
      exact absurd (Finset.mem_range.mpr hm) h
  have h3 : (∏ i ∈ range m, (if i < m then V.uniformizer ^ (d i) else 1))
      = V.uniformizer ^ (∑ i ∈ range m, d i) := by
    rw [Finset.prod_congr rfl (fun i hi => by rw [if_pos (Finset.mem_range.mp hi)])]
    exact V.prod_uniformizer_zpow _ _
  rw [renormProd, h1, h2, h3]
  have hcomm : V.uniformizer ^ k * (V.uniformizer ^ (-(k + ∑ j ∈ range m, d j)) * g *
      V.uniformizer ^ (∑ i ∈ range m, d i))
      = (V.uniformizer ^ k * V.uniformizer ^ (-(k + ∑ j ∈ range m, d j)) *
        V.uniformizer ^ (∑ i ∈ range m, d i)) * g := by
    simp [mul_comm, mul_left_comm]
  rw [hcomm, ← zpow_add, ← zpow_add]
  simp
