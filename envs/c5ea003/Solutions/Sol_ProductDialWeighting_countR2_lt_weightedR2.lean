-- Prove2me | solution 1 for ProductDialWeighting.countR2_lt_weightedR2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:52:59.697562+00:00
-- url     : https://prove2.me/submissions/2dc1ba26-e4a4-4553-9416-862e7c810efc

-- Sol generated from Algebra/ProductDialWeighting.lean
import Mathlib
import Definitions.Def_Algebra_ProductDialWeighting
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


/-- **Exact factorisation** of the count dial's explained variance. -/
theorem countR2_eq_flatness_mul_weightedR2 {S T : Finset ι} (a : ι → ℝ)
    (hcard : 0 < T.card) (hTa : 0 < ∑ i ∈ T, (a i) ^ 2)
    (hpos : 0 < ∑ i ∈ S, (a i) ^ 2) :
    countR2 S T a = flatness T a * weightedR2 S T a := by
  have hcard' : (0 : ℝ) < T.card := by exact_mod_cast hcard
  rw [countR2, flatness, weightedR2]
  field_simp

/-- Lagrange's identity in the form needed: the Cauchy–Schwarz defect is the
mean square of all pairwise differences. -/
theorem sum_sq_pairwise_diff (T : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ T, ∑ j ∈ T, (a i - a j) ^ 2
      = 2 * ((T.card : ℝ) * ∑ i ∈ T, (a i) ^ 2 - (∑ i ∈ T, a i) ^ 2) := by
  have h1 : ∀ i : ι, ∑ j ∈ T, (a i - a j) ^ 2
      = (T.card : ℝ) * (a i) ^ 2 - 2 * a i * (∑ j ∈ T, a j) + ∑ j ∈ T, (a j) ^ 2 := by
    intro i
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
  simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- A non-constant profile has a strictly positive Cauchy–Schwarz defect. -/
theorem sq_sum_lt_card_mul_sum_sq {T : Finset ι} {a : ι → ℝ} {i₀ j₀ : ι}
    (hi : i₀ ∈ T) (hj : j₀ ∈ T) (hne : a i₀ ≠ a j₀) :
    (∑ i ∈ T, a i) ^ 2 < (T.card : ℝ) * ∑ i ∈ T, (a i) ^ 2 := by
  have hterm : (0 : ℝ) < (a i₀ - a j₀) ^ 2 := by
    have : a i₀ - a j₀ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hinner : (a i₀ - a j₀) ^ 2 ≤ ∑ j ∈ T, (a i₀ - a j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (a i₀ - a j) ^ 2) (fun j _ => sq_nonneg _) hj
  have houter : (∑ j ∈ T, (a i₀ - a j) ^ 2) ≤ ∑ i ∈ T, ∑ j ∈ T, (a i - a j) ^ 2 :=
    Finset.single_le_sum (f := fun i => ∑ j ∈ T, (a i - a j) ^ 2)
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) hi
  have hid := sum_sq_pairwise_diff T a
  linarith


/-! ## 4. Saturation of the weighted dial -/






/-! ## 5. The harmonic amplitude model: saturation versus dilution -/















open ProductDialWeighting in
theorem solution{S T : Finset ι} {a : ι → ℝ} {i₀ j₀ : ι}
    (hi : i₀ ∈ T) (hj : j₀ ∈ T) (hne : a i₀ ≠ a j₀)
    (hpos : 0 < ∑ i ∈ S, (a i) ^ 2) :
    countR2 S T a < weightedR2 S T a := by
  have hcard : 0 < T.card := Finset.card_pos.mpr ⟨i₀, hi⟩
  have hcard' : (0 : ℝ) < T.card := by exact_mod_cast hcard
  have hdefect := sq_sum_lt_card_mul_sum_sq hi hj hne
  have hTa : 0 < ∑ i ∈ T, (a i) ^ 2 := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)) :
        (0 : ℝ) ≤ ∑ i ∈ T, (a i) ^ 2) with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero] at hdefect
      nlinarith [sq_nonneg (∑ i ∈ T, a i)]
  have hflat : flatness T a < 1 := by
    rw [flatness, div_lt_one (by positivity)]
    exact hdefect
  have hw : 0 < weightedR2 S T a := div_pos hTa hpos
  rw [countR2_eq_flatness_mul_weightedR2 a hcard hTa hpos]
  nlinarith
