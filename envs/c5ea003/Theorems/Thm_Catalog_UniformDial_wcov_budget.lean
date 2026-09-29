-- Prove2me | Theorems.Thm_Catalog_UniformDial_wcov_budget
-- name    : Catalog.UniformDial.wcov_budget
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:03:45.359598+00:00
-- url     : https://prove2.me/theorems/bb5a060b-01cf-460c-a5b2-6db542769fa0
-- title:
--   Concordance budget.
-- statement:
--   **Concordance budget.**  For any regime whose per-key mass lies in `[ε, M]`, the dial
--   is bounded below by `ε² · C − M² · Δ`, with `C`, `Δ` the population's concordant and
--   discordant pair masses.
--
--   ```lean
--   theorem Catalog.UniformDial.wcov_budget{p x y : ι → ℝ} {ε M : ℝ} (hp : ∑ i, p i = 1) (hε : 0 ≤ ε)
--       (hlo : ∀ i, ε ≤ p i) (hhi : ∀ i, p i ≤ M) :
--       ε ^ 2 * concordanceMass x y - M ^ 2 * discordanceMass x y ≤ 2 * wcov p x y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/UniformDialRegimeHomotopy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/UniformDialRegimeHomotopy.lean#L167

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












/-! ### The concordance budget: how unbalanced can a draw get? -/

theorem Catalog.UniformDial.wcov_budget{p x y : ι → ℝ} {ε M : ℝ} (hp : ∑ i, p i = 1) (hε : 0 ≤ ε)
    (hlo : ∀ i, ε ≤ p i) (hhi : ∀ i, p i ≤ M) :
    ε ^ 2 * concordanceMass x y - M ^ 2 * discordanceMass x y ≤ 2 * wcov p x y := by sorry
