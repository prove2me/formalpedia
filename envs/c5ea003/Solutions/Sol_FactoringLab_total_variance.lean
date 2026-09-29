-- Prove2me | solution 1 for FactoringLab.total_variance
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:16:19.536191+00:00
-- url     : https://prove2.me/submissions/8f217f4e-cd88-4d19-8847-02541ef6efcb

-- Sol generated from Probability/BandSpread.lean
import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
import Theorems.Thm_FactoringLab_cov_centered
import Theorems.Thm_FactoringLab_expect_bandMean
import Theorems.Thm_FactoringLab_structural_orthogonality
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

/-- The empirical variance as a sum of squared deviations. -/
theorem variance_eq_sum_sq (Ω : Finset ι) (X : ι → ℝ) :
    variance Ω X = (∑ i ∈ Ω, (X i - expect Ω X) ^ 2) / Ω.card := by
  rw [variance, cov_centered Ω X X]
  exact congrArg (· / (Ω.card : ℝ)) (Finset.sum_congr rfl fun i _ => by ring)


/-! ## The law of total variance -/








/-- `bandMeanFn` applied to the band label of `i` is exactly the band mean at `i`. -/
lemma bandMeanFn_comp (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (i : ι) :
    bandMeanFn Ω n Y (n i) = bandMean Ω n Y i := by
  simp [bandMeanFn, bandMean, band]

open FactoringLab in
theorem solution(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) :
    variance Ω Y
      = (∑ i ∈ Ω, (Y i - bandMean Ω n Y i) ^ 2) / Ω.card
        + variance Ω (bandMean Ω n Y) := by
  have hcross :
      ∑ i ∈ Ω, (bandMean Ω n Y i - expect Ω Y) * (Y i - bandMean Ω n Y i) = 0 := by
    have h := structural_orthogonality Ω n Y (fun k => bandMeanFn Ω n Y k - expect Ω Y)
    simpa [bandMeanFn_comp] using h
  have hsplit : ∑ i ∈ Ω, (Y i - expect Ω Y) ^ 2
      = ∑ i ∈ Ω, (Y i - bandMean Ω n Y i) ^ 2
        + ∑ i ∈ Ω, (bandMean Ω n Y i - expect Ω Y) ^ 2 := by
    have hexp : ∀ i, (Y i - expect Ω Y) ^ 2
        = (Y i - bandMean Ω n Y i) ^ 2 + (bandMean Ω n Y i - expect Ω Y) ^ 2
          + 2 * ((bandMean Ω n Y i - expect Ω Y) * (Y i - bandMean Ω n Y i)) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, hcross, mul_zero, add_zero]
  rw [variance_eq_sum_sq Ω Y, variance_eq_sum_sq Ω (bandMean Ω n Y),
    expect_bandMean Ω n Y, hsplit, add_div]
