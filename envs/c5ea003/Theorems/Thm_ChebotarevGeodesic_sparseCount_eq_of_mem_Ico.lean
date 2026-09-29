-- Prove2me | Theorems.Thm_ChebotarevGeodesic_sparseCount_eq_of_mem_Ico
-- name    : ChebotarevGeodesic.sparseCount_eq_of_mem_Ico
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:25:10.14177+00:00
-- url     : https://prove2.me/theorems/f61e877b-0797-42f8-b82a-57dd78576c3f
-- title:
--   `sparseCount Î´` is constant, equal to `n^{1/Î´}`, on the interval
-- statement:
--   `sparseCount Î´` is constant, equal to `n^{1/Î´}`, on the interval
--   `[n^{1/Î´}, (n+1)^{1/Î´})`.
--
--   ```lean
--   theorem ChebotarevGeodesic.sparseCount_eq_of_mem_Ico{δ y : ℝ} (hδ0 : 0 < δ) {n : ℕ} (hn : 1 ≤ n)
--       (h1 : ((n : ℝ)) ^ (1 / δ) ≤ y) (h2 : y < ((n : ℝ) + 1) ^ (1 / δ)) :
--       sparseCount δ y = ((n : ℝ)) ^ (1 / δ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicGaps.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicGaps.lean#L250

-- Thm stub generated from Shared/ChebotarevGeodesicGaps.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicGaps
import Definitions.Def_Shared_ChebotarevGeodesicTorus
/-
# Short-interval (additive window) gaps for Chebotarev geodesic counting functions

Motivated by *"Chebotarev geodesic theorem: non-split case"* and continuing the development in
`Shared.ChebotarevGeodesic`, `Shared.ChebotarevGeodesicEffective` and
`Shared.ChebotarevGeodesicTorus`.

`eventually_lt_of_window` (in `ChebotarevGeodesicEffective.lean`) proves the *multiplicative*
window statement: if `π x = c x^β + O(x^{θ+ε})` with `θ < β`, then every dilated window
`[x, λ x]`, `λ > 1`, eventually contains a new geodesic.  This file proves the much stronger
**additive** (short-interval) statement predicted by conjecture C4 of `FUTURE_DIRECTIONS.md`:

* `rpow_bernoulli_add_le` : the scaled Bernoulli inequality
  `x^β + β x^{β-1} h ≤ (x+h)^β` for `β ≥ 1`, `x > 0`, `h ≥ 0`;
* `eventually_lt_of_additive_window` : for every exponent `γ` with
  `1 - (β - θ) < γ ≤ 1` the interval `[x, x + x^{γ}]` eventually contains a point counted
  by `π`;
* `exists_additive_window_threshold` : the same statement in explicit `∃ X₀, ∀ x ≥ X₀` form;
* `chebotarev_gap_25_36` : the numerical instance of the paper — with main term `c·x` and
  exponent `25/36`, consecutive geodesics of a fixed conjugacy class are at distance
  `≪ x^{25/36 + ε}`;
* `torusCount_eq_of_mem_Ico`, `torusCount_no_short_gaps` : the *sharpness boundary*.  For the
  single non-split torus, whose main term is logarithmic rather than a positive power, the
  conclusion fails for **every** `γ < 1`: there are arbitrarily large `x` with no geodesic at
  all in `[x, x + x^{γ}]`.  So a power-size main term is not a technical convenience in
  `eventually_lt_of_additive_window`, it is exactly what makes short-interval gaps possible.
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic

/-! ## A scaled Bernoulli inequality -/


/-! ## Geodesics in short intervals -/




/-! ## Sharpness: a logarithmic main term admits arbitrarily long gaps -/



/-! ## The critical window exponent is exactly `1 - (β - θ)`

The torus model above shows that *some* hypothesis on the size of the main term is needed.  We
now show that the numerical threshold `1 - (β - θ)` of `eventually_lt_of_additive_window` is
itself optimal, by exhibiting for every `θ ∈ [0,1)` a counting function with main term exactly
`x` and error exponent `θ` whose jumps are spaced `≍ x^{θ}` apart.  Writing `δ = 1 - θ`, the
example is the *`δ`-sparse counter*

  `sparseCount δ x = ⌊x^δ⌋^{1/δ}`,

which is constant on each interval `[n^{1/δ}, (n+1)^{1/δ})`. -/

theorem ChebotarevGeodesic.sparseCount_eq_of_mem_Ico{δ y : ℝ} (hδ0 : 0 < δ) {n : ℕ} (hn : 1 ≤ n)
    (h1 : ((n : ℝ)) ^ (1 / δ) ≤ y) (h2 : y < ((n : ℝ) + 1) ^ (1 / δ)) :
    sparseCount δ y = ((n : ℝ)) ^ (1 / δ) := by sorry
