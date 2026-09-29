-- Prove2me | Definitions.Def_Combinatorics_UniformDialRegimeHomotopy
-- name    : Combinatorics_UniformDialRegimeHomotopy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:56:54.050016+00:00
-- url     : https://prove2.me/theorems/6a6bccd0-a2eb-4305-a502-33347dbec4cf
-- title:
--   Aether Catalog definitions — Combinatorics_UniformDialRegimeHomotopy
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.UniformDialRegimeHomotopy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/UniformDialRegimeHomotopy.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
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

namespace Catalog.UniformDial

variable {ι : Type*} [Fintype ι]

/-! ### Homotopy between two draw regimes -/

/-- Linear interpolation between two weightings. -/
noncomputable def mixWeights (p q : ι → ℝ) (t : ℝ) : ι → ℝ := fun i => (1 - t) * p i + t * q i





/-- The cross term of two regimes: half the total pair mass a *product* draw assigns to
the concordance products. -/
noncomputable def crossTerm (p q x y : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, p i * q j * ((x i - x j) * (y i - y j))






/-! ### The concordance budget: how unbalanced can a draw get? -/

/-- Total concordant pair mass of the population (regime-free). -/
noncomputable def concordanceMass (x y : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, max ((x i - x j) * (y i - y j)) 0

/-- Total discordant pair mass of the population (regime-free). -/
noncomputable def discordanceMass (x y : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, max (-((x i - x j) * (y i - y j))) 0







end Catalog.UniformDial


