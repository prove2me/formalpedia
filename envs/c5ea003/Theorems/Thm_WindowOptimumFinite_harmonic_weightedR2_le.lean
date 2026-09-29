-- Prove2me | Theorems.Thm_WindowOptimumFinite_harmonic_weightedR2_le
-- name    : WindowOptimumFinite.harmonic_weightedR2_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:02:25.944992+00:00
-- url     : https://prove2.me/theorems/1ab62526-4ecf-423d-ad06-e0bc44ce1b43
-- title:
--   Matching upper bound on saturation.
-- statement:
--   **Matching upper bound on saturation.**  A window of size `n` never explains
--   more than `1 - 1/(8n)` of the explainable variance once the population reaches
--   `2n`: saturation is of order `1/n` exactly, so the window size is a tolerance
--   parameter and not a scale parameter.
--
--   ```lean
--   theorem WindowOptimumFinite.harmonic_weightedR2_le{n N : ℕ} (hn : 0 < n) (hN : 2 * n ≤ N) :
--       weightedR2 (range N) (range n) harmonicAmp ≤ 1 - 1 / (8 * (n : ℝ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/WindowOptimumFinite.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/WindowOptimumFinite.lean#L197

-- Thm stub generated from Algebra/WindowOptimumFinite.lean
import Mathlib
import Definitions.Def_Algebra_ProductDialWeighting
import Definitions.Def_Algebra_WindowOptimumFinite
/-
# The window is stronger, not shifted: finiteness of the count-dial optimum

Formal core of experiment **577** (paper 227), verdict part
(`WINDOW-STRONGER-NOT-SHIFTED`) and dispersion bookkeeping.

## The verdict to be explained

The pre-registered alternative `H1` was a *scale shift*: that the informative
quadratic-residue window moves outwards as the cutoff `B` grows, so that some
larger `B` would beat `B = 400`.  All four shift candidates failed, and the
measured sweep of the equal-weight count dial

  `B = 400 : R² = .3207`, `4000 : .0241`, `4·10⁴ : .0150`, `10⁵ : .0000`,
  `10⁶ : .0277`

instead *decays*.  The weighted dial, by contrast, is monotone and saturates.

## What is proved here

Working in the harmonic amplitude model of `ProductDialWeighting`:

* `WindowOptimumFinite.countR2_le_countScore` — the count dial's explained
  variance is bounded by the ambient-free score `H_n² / n`.
* `WindowOptimumFinite.countScore_tendsto_zero` — that score tends to `0`:
  there is no escape to larger windows.
* `WindowOptimumFinite.exists_window_optimum` — **the refutation of the scale
  shift**: the count-dial score attains a *global maximum at a finite window*
  `B*`.  Enlarging the window past `B*` can never help; the optimum does not run
  off to infinity.
* `WindowOptimumFinite.weighted_never_hurts` — the contrasting behaviour of the
  weighted dial: it is monotone in the window, so its "optimum" is the whole
  population, and by the saturation theorem it is already essentially attained
  at a small window.
* `WindowOptimumFinite.weighted_saturated_at_400` — at the published window the
  weighted dial captures at least `99.75%` of what any larger window can.
* `WindowOptimumFinite.harmonic_weightedR2_le` — the matching *lower* bound:
  a window of size `n` never explains more than `1 - 1/(8n)`, so the saturation
  rate is of order `1/n` exactly and the window size is a tolerance parameter,
  not a scale parameter.
* `WindowOptimumFinite.reading_ratio` — the exact algebra relating the two
  dispersion readings ("fraction of raw overdispersion" versus "fraction of
  excess above Poisson"): their ratio is `(D-1)/D`, *independent of the size of
  the reduction*.
* `WindowOptimumFinite.readings_consistent` — the two measured dial rows
  (`33.43% / 42.06%` and `48.51% / 61.00%`) imply the same baseline dispersion
  to within `0.03`, which is why both readings may be quoted for the same
  population.
-/

open WindowOptimumFinite

open Finset Filter Topology ProductDialWeighting

/-! ## 1. The ambient-free count score -/










/-! ### 1b. The saturation rate is exactly of order `1/n`

The upper bound `1 - 1/n ≤ weightedR²` of `harmonic_weightedR2_ge` is matched by a
lower bound of the same order, so "how large a window do I need" is a question
about the *tolerance* only, never about the size of the ambient population. -/

theorem WindowOptimumFinite.harmonic_weightedR2_le{n N : ℕ} (hn : 0 < n) (hN : 2 * n ≤ N) :
    weightedR2 (range N) (range n) harmonicAmp ≤ 1 - 1 / (8 * (n : ℝ)) := by sorry
