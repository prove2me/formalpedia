-- Prove2me | solution 1 for ProductDialWeighting.saturation_versus_dilution
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:01:56.355723+00:00
-- url     : https://prove2.me/submissions/d516ed66-68dd-4232-a85f-6741ee372161

-- Sol generated from Algebra/ProductDialWeighting.lean
import Mathlib
import Definitions.Def_Algebra_ProductDialWeighting
import Theorems.Thm_ProductDialWeighting_harmonic_countR2_le
import Theorems.Thm_ProductDialWeighting_harmonic_weightedR2_ge
import Theorems.Thm_ProductDialWeighting_log_sq_div_tendsto_zero
/-
# Why the `1/ℓ`-weighted dial is the law: saturation versus dilution

Formal core of experiment **577** (paper 227), analytic part.

## The experimental facts to be explained

Two covariates were built from the quadratic-residue pattern of `N` at the
primes `ℓ ≤ B`:

* the **count dial**  `C(B) = #{ℓ ≤ B : ℓ is a QR prime for N}` (equal weights);
* the **harmonically weighted dial** `W(B) = ∑_{QR ℓ ≤ B} 1/ℓ`.

Measured explained variance against the target:

| `B`   | count `R²` | weighted `R²` |
|-------|-----------|----------------|
| 400   | .3207     | .4731          |
| 4000  | .0241     | —              |
| 4·10⁴ | .0150     | —              |
| 10⁵   | .0000     | —              |
| 10⁶   | .0277     | .4786          |

So: **extending the window dilutes the count dial, while the weighted dial
saturates** (corr(W(10⁶), W(400)) = .999).

## What is proved here

The experiment's two-sided phenomenon is a theorem about *linear covariates in
an orthonormal signal model*, not an accident of the arithmetic population.
Model the target as `s = ∑_{i ∈ S} a i • e i` with `e` orthonormal (independent
per-prime contributions of amplitude `a i`); a *window* `T ⊆ S` gives

* the count covariate `∑_{i ∈ T} e i`, and
* the weighted covariate `∑_{i ∈ T} a i • e i`.

* `ProductDialWeighting.R2_of_orthonormal` — the squared correlation of any
  coefficient covariate with the target is the discrete Cauchy–Schwarz ratio.
* `ProductDialWeighting.countDialR2_eq`, `ProductDialWeighting.weightedDialR2_eq`
  — the two dials realise `countR2` and `weightedR2`.
* `ProductDialWeighting.countR2_le_weightedR2` — **the weighted dial dominates
  the count dial at every window**, by Cauchy–Schwarz.  (Measured: `.3207 ≤ .4731`.)
* `ProductDialWeighting.countR2_eq_flatness_mul_weightedR2` and
  `ProductDialWeighting.countR2_lt_weightedR2` — the loss is *exactly* a profile
  flatness factor, and it is strict whenever the amplitudes are non-constant on
  the window (Lagrange's identity for the Cauchy–Schwarz defect).
* `ProductDialWeighting.weightedR2_mono`, `weightedR2_le_one`,
  `weightedR2_eq_one` — the weighted dial is monotone in the window, capped by
  `1`, and exactly `1` at the full window.
* `ProductDialWeighting.weightedR2_ge_one_sub_tail` and the harmonic instance
  `harmonic_weightedR2_ge` — **saturation**: with amplitudes `a i = 1/(i+1)` the
  window `[0, n)` already explains at least `1 - 1/n` of everything the whole
  population can explain, uniformly in the ambient population size.
* `ProductDialWeighting.harmonic_countR2_le` and
  `ProductDialWeighting.harmonic_countR2_le_eventually` — **dilution**: the same
  amplitudes make the equal-weight count `R²` at most `(1 + log n)²/n`, which
  tends to `0`.  Equal weighting *buries* the informative small primes.
* `ProductDialWeighting.saturation_versus_dilution` — the two phenomena, in one
  statement: for every `ε > 0` all sufficiently large windows have weighted
  `R² ≥ 1 - ε` while count `R² ≤ ε`.

The arithmetic input (`a ℓ ≍ 1/ℓ`, the density of the residue class) is exactly
the hypothesis under which the model reproduces both measured columns.
-/

open ProductDialWeighting

open Finset Filter Topology

/-! ## 1. Squared correlation in an orthonormal signal model -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*}




/-! ## 2. The two dials -/




variable [DecidableEq ι]






/-! ## 3. Weighted dominates count -/


/-! ### 3b. The exact loss factor: profile flatness

The count dial is the weighted dial *times* a purely geometric factor measuring
how flat the amplitude profile is on the window.  A `1/ℓ` profile is very far
from flat, which is precisely why equal weighting loses so much. -/






/-! ## 4. Saturation of the weighted dial -/






/-! ## 5. The harmonic amplitude model: saturation versus dilution -/












/-- **Dilution.**  The count dial's explained variance is eventually below any
tolerance, uniformly over ambient populations containing the window. -/
theorem harmonic_countR2_le_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n N : ℕ, n₀ ≤ n → n ≤ N →
      countR2 (range N) (range n) harmonicAmp ≤ ε := by
  have h := log_sq_div_tendsto_zero
  rw [Metric.tendsto_atTop] at h
  obtain ⟨m, hm⟩ := h ε hε
  refine ⟨max m 1, by positivity, fun n N hn hnN => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right m 1) hn)
  have hmn : m ≤ n := le_trans (le_max_left m 1) hn
  have hd := hm n hmn
  rw [Real.dist_eq, sub_zero] at hd
  exact le_trans (harmonic_countR2_le hn1 hnN) (le_of_lt (lt_of_abs_lt hd))



open ProductDialWeighting in
theorem solution(ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n N : ℕ, n₀ ≤ n → n ≤ N →
      1 - ε ≤ weightedR2 (range N) (range n) harmonicAmp ∧
      countR2 (range N) (range n) harmonicAmp ≤ ε := by
  obtain ⟨n₁, hn₁pos, hn₁⟩ := harmonic_countR2_le_eventually ε hε
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (1 / ε)
  refine ⟨max n₁ (n₂ + 1), by positivity, fun n N hn hnN => ?_⟩
  have hna : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnb : n₂ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 0 < n := by omega
  refine ⟨?_, hn₁ n N hna hnN⟩
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlt : (1 / ε) < (n : ℝ) := by
    refine lt_of_lt_of_le hn₂ ?_
    exact_mod_cast (by omega : n₂ ≤ n)
  have hle : 1 / (n : ℝ) ≤ ε := by
    rw [div_le_iff₀ hnpos']
    rw [div_lt_iff₀ hε] at hlt
    linarith
  have hsat := harmonic_weightedR2_ge hnpos hnN
  linarith
