-- Prove2me | Theorems.Thm_Catalog_UniformDial_wcov_mix
-- name    : Catalog.UniformDial.wcov_mix
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:03:59.528325+00:00
-- url     : https://prove2.me/theorems/95db06d3-1100-455b-80f5-bdea4e2c4696
-- title:
--   The dial is an exact quadratic along a regime homotopy.
-- statement:
--   **The dial is an exact quadratic along a regime homotopy.**
--
--   ```lean
--   theorem Catalog.UniformDial.wcov_mix{p q x y : ι → ℝ} (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (t : ℝ) :
--       wcov (mixWeights p q t) x y
--         = (1 - t) ^ 2 * wcov p x y + 2 * t * (1 - t) * crossTerm p q x y
--           + t ^ 2 * wcov q x y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/UniformDialRegimeHomotopy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/UniformDialRegimeHomotopy.lean#L77

-- Thm stub generated from Combinatorics/UniformDialRegimeHomotopy.lean
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
import Definitions.Def_Combinatorics_UniformDialRegimeHomotopy
/-
# Regime homotopy and the concordance budget of the yield dial

Second cycle of the `UniformDial` thread (see `Combinatorics.UniformDialDrawInvariance`
for the pairwise identity and the sign-invariance theorems).

Two structural questions are settled here.

**(1) What happens *between* two draw regimes?**  Interpolating linearly from a balanced
regime `p` to a genuinely unbalanced regime `q` gives a one-parameter family
`mixWeights p q t`.  `wcov_mix` shows the dial reading is an *exact quadratic* in `t`
with an explicit cross term, and `wcov_mix_ge` / `wcov_mix_ge_half_min` show that for a
comonotone population the reading along the whole homotopy never drops below
`½ · min(endpoint readings)`.  So the dial cannot be diluted *anywhere* on the path, not
merely at the two measured endpoints — a strictly stronger statement than comparing two
experiments.

**(2) How unbalanced may a draw be before the dial could break?**  `wcov_budget` bounds
the dial from below by `ε²·C − M²·Δ`, where `C` and `Δ` are the total concordant and
discordant pair masses of the *population* (regime-free quantities) and `[ε, M]` bounds
the regime's per-key mass.  `dial_pos_of_concordance_ratio` turns this into a triage
rule: the dial is positive in *every* regime whose mass ratio `κ = M/ε` satisfies
`κ² · Δ < C`.  Dilution is therefore impossible until the draw's conditioning number
exceeds an explicit population-determined threshold.
-/

open Finset

open Catalog.UniformDial

variable {ι : Type*} [Fintype ι]

/-! ### Homotopy between two draw regimes -/

theorem Catalog.UniformDial.wcov_mix{p q x y : ι → ℝ} (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (t : ℝ) :
    wcov (mixWeights p q t) x y
      = (1 - t) ^ 2 * wcov p x y + 2 * t * (1 - t) * crossTerm p q x y
        + t ^ 2 * wcov q x y := by sorry
