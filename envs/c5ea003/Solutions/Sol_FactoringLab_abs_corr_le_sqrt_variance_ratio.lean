-- Prove2me | solution 1 for FactoringLab.abs_corr_le_sqrt_variance_ratio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:24:08.237114+00:00
-- url     : https://prove2.me/submissions/398dd183-7faa-4101-bcf4-31b931e4c8a3

-- Sol generated from Probability/BandSpread.lean
import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
import Theorems.Thm_FactoringLab_cov_centered
import Theorems.Thm_FactoringLab_cov_sq_le_variance_mul_variance_bandMean
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

/-- The empirical variance is nonnegative. -/
theorem variance_nonneg (Ω : Finset ι) (X : ι → ℝ) : 0 ≤ variance Ω X := by
  rw [variance_eq_sum_sq]
  exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Nat.cast_nonneg _)

/-! ## The law of total variance -/








open FactoringLab in
theorem solution(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
    (g : κ → ℝ) (hY : 0 < variance Ω Y) :
    |corr Ω (fun i => g (n i)) Y|
      ≤ Real.sqrt (variance Ω (bandMean Ω n Y) / variance Ω Y) := by
  set X : ι → ℝ := fun i => g (n i) with hX
  set vX := variance Ω X with hvX
  set vB := variance Ω (bandMean Ω n Y) with hvB
  have hvX0 : 0 ≤ vX := variance_nonneg Ω X
  have hvB0 : 0 ≤ vB := variance_nonneg Ω _
  have hkey : (cov Ω X Y) ^ 2 ≤ vX * vB :=
    cov_sq_le_variance_mul_variance_bandMean Ω n Y g
  have habs : |cov Ω X Y| ≤ Real.sqrt vX * Real.sqrt vB := by
    have h1 : |cov Ω X Y| = Real.sqrt ((cov Ω X Y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    rw [h1, ← Real.sqrt_mul hvX0]
    exact Real.sqrt_le_sqrt hkey
  rcases eq_or_lt_of_le hvX0 with hzero | hpos
  · -- a constant invariant has zero variance, hence zero correlation
    have : corr Ω X Y = 0 := by
      unfold corr
      rw [← hvX, ← hzero, Real.sqrt_zero, zero_mul, div_zero]
    rw [this, abs_zero]
    exact Real.sqrt_nonneg _
  · have hsX : 0 < Real.sqrt vX := Real.sqrt_pos.2 hpos
    have hsY : 0 < Real.sqrt (variance Ω Y) := Real.sqrt_pos.2 hY
    have hcorr : |corr Ω X Y| = |cov Ω X Y| / (Real.sqrt vX * Real.sqrt (variance Ω Y)) := by
      unfold corr
      rw [abs_div, abs_of_pos (mul_pos hsX hsY)]
    rw [hcorr, Real.sqrt_div' _ (le_of_lt hY)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc |cov Ω X Y| * Real.sqrt (variance Ω Y)
        ≤ (Real.sqrt vX * Real.sqrt vB) * Real.sqrt (variance Ω Y) := by
          exact mul_le_mul_of_nonneg_right habs (Real.sqrt_nonneg _)
      _ = Real.sqrt vB * (Real.sqrt vX * Real.sqrt (variance Ω Y)) := by ring
