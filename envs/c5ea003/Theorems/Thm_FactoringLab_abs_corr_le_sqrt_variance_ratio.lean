-- Prove2me | Theorems.Thm_FactoringLab_abs_corr_le_sqrt_variance_ratio
-- name    : FactoringLab.abs_corr_le_sqrt_variance_ratio
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:29:11.362124+00:00
-- url     : https://prove2.me/theorems/2c5ae5a7-fab3-4d5b-bee9-593c8f5e6e05
-- title:
--   The band-spread bound on correlations.
-- statement:
--   **The band-spread bound on correlations.**  For every invariant `g ∘ n`
--   computable from the band label alone, the Pearson correlation with the target
--   is controlled by the ratio of the *variance of the band means* to the variance
--   of the target — uniformly in `g`.
--
--   ```lean
--   theorem FactoringLab.abs_corr_le_sqrt_variance_ratio(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
--       (g : κ → ℝ) (hY : 0 < variance Ω Y) :
--       |corr Ω (fun i => g (n i)) Y|
--         ≤ Real.sqrt (variance Ω (bandMean Ω n Y) / variance Ω Y) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/BandSpread.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/BandSpread.lean#L89

-- Thm stub generated from Probability/BandSpread.lean
import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
/-
# The Band-Spread Law (Factoring Lab, Phase A v19c — cycle 2)

Formalizing the *reduction* asserted by **Conjecture 4** of
`FUTURE_DIRECTIONS.md`: the whole empirical near-equal-`N` programme collapses
to a single analytic quantity, the **spread of the band means**.

The previous cycle proved the hypothesis-free Cauchy–Schwarz bound
`FactoringLab.cov_sq_le_variance_mul_variance_bandMean`:
`cov(g∘n, Y)² ≤ Var(g∘n) · Var(E[Y | n])`.
Here that inequality is converted into the statement the conjecture actually
uses, about the *correlation*:

* `FactoringLab.variance_nonneg` — the empirical variance is nonnegative;
* `FactoringLab.abs_corr_le_sqrt_variance_ratio` — for **every** invariant
  computable from the band label alone,
  `|corr(g∘n, Y)| ≤ √( Var(E[Y | n]) / Var Y )`,
  with no hypothesis beyond `Var Y > 0`;
* `FactoringLab.band_spread_law` — the conjecture's shape: if the band means
  have spread at most `ε · Var Y`, then every `N`-only invariant has
  `|corr| ≤ √ε`;
* `FactoringLab.corr_eq_zero_of_bandMean_variance_zero` — the degenerate case:
  zero spread forces exactly zero correlation;
* `FactoringLab.total_variance` — the law of total variance for the band
  decomposition, `Var Y = (within-band error) + Var(E[Y | n])`, which identifies
  the band spread as exactly the fraction of the variance the band label
  explains, and `FactoringLab.abs_corr_le_sqrt_explained_fraction`, the
  resulting bound on every `N`-only correlation.

So the near-equal-`N` test is not a heuristic: the measured correlations of
`N`-only invariants are bounded by an intrinsic property of the population,
uniformly over all invariants.  What remains of Conjecture 4 is purely
analytic — an estimate of `Var(E[p | N])` for semiprimes in a size band, which
is a statement about the distribution of the smaller factor and involves no
invariant at all.
-/

open FactoringLab

variable {ι κ : Type*} [DecidableEq κ]



/-! ## The law of total variance -/

theorem FactoringLab.abs_corr_le_sqrt_variance_ratio(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
    (g : κ → ℝ) (hY : 0 < variance Ω Y) :
    |corr Ω (fun i => g (n i)) Y|
      ≤ Real.sqrt (variance Ω (bandMean Ω n Y) / variance Ω Y) := by sorry
