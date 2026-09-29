-- Prove2me | Theorems.Thm_KappaDial_card_range_val_cell
-- name    : KappaDial.card_range_val_cell
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:19:09.04453+00:00
-- url     : https://prove2.me/theorems/9c2353dd-8ad6-4989-944c-e22a54e22aeb
-- title:
--   One prime coordinate of the valuation ladder: among the `p^{e+1}` residues of the
-- statement:
--   One prime coordinate of the valuation ladder: among the `p^{e+1}` residues of the
--   refined period exactly `p - 1` have valuation exactly `e`.
--
--   ```lean
--   theorem KappaDial.card_range_val_cell(p e : ℕ) (hp : p.Prime) :
--       ((range (p ^ (e + 1))).filter (fun v => p ^ e ∣ v ∧ ¬ p ^ (e + 1) ∣ v)).card = p - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/KappaDialRefinement.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/KappaDialRefinement.lean#L106

-- Thm stub generated from Combinatorics/KappaDialRefinement.lean
import Mathlib
import Definitions.Def_Combinatorics_KappaDialRefinement
import Definitions.Def_Combinatorics_KappaRateDial
/-
# Refinements of the κ rate–dial: coprime-scale equidistribution, the valuation ladder,
# and the effective size of a cell sweep

Building on `Combinatorics.KappaRateDial`, this file pushes the "rate dial, not a position
dial" dichotomy in three directions.

1. **A coprime-statistic no-go theorem** (`cellCount_coprime_statistic`, and its
   equidistribution corollary `cellCount_coprime_residue`). The absence of a positional
   signal is not merely a statement about whole period blocks: for *any* modulus `M` coprime
   to the period `L` and *any* statistic `Q` depending only on `v mod M`, the divisibility
   cell and the event `Q` are *exactly independent* over one common period. In particular
   each residue class mod `M` receives exactly `κ(σ)` members of the cell inside `[0, L·M)`.
   A divisibility cell therefore carries *no* information about any coprime-measurable
   observable, uniformly.

2. **The valuation ladder** (`card_valPeriod_eq`). Refining "`p ∣ v`" to "`v_p(v) = e p`"
   produces, over the refined period `∏ p^{e p + 1}`, a cell of size *exactly* `∏ (p - 1)`,
   **independently of the exponents** `e`. Sharpening the resolution of the dial therefore
   changes only the period (the denominator), never the numerator: the rate dial is a pure
   geometric ladder `∏ p^{-e p} (1 - 1/p)`.

3. **Effective sweep size** (`sweep_image_card_le`, `sweepValues_card_eq_iff`). Because the
   prime `2` is a dead coordinate, a sweep over all `2^{|P|}` divisibility cells explores at
   most `2^{|P| - 1}` distinct rate values when `2 ∈ P`; and it attains that maximum exactly
   when the numbers `p - 1` over the odd primes of `P` have pairwise distinct subset
   products. Quantifying the effective number of degrees of freedom of a cell sweep is
   exactly what a max-statistic selection correction needs. The criterion is not vacuous:
   `sweep_collision_3_7_13` exhibits a prime set where it fails.

## Lab notes

`P = {2,3,5,7}`, `L = 210`, all-cleared cell, `M = 11`: each of the 11 residue classes mod
`11` inside `[0, 2310)` contains exactly `48` totatives of `210` — checked by the general
theorem and instantiated in `cellCount_coprime_residue_example`.

Valuation ladder for `p = 3`, `e = 0,1,2`: cells of size `2` inside periods `3, 9, 27`, i.e.
densities `2/3, 2/9, 2/27` — a clean geometric ladder with constant numerator.
-/


open Finset

open KappaDial


/-! ## 1. Equidistribution across residue classes at any coprime scale -/




/-! ## 2. The valuation ladder: exact `p`-adic valuation cells -/

theorem KappaDial.card_range_val_cell(p e : ℕ) (hp : p.Prime) :
    ((range (p ^ (e + 1))).filter (fun v => p ^ e ∣ v ∧ ¬ p ^ (e + 1) ∣ v)).card = p - 1 := by sorry
