-- Prove2me | solution 1 for WhichFactorWall.imbalance_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:08:27.410859+00:00
-- url     : https://prove2.me/submissions/27cff85b-252d-4884-be90-5c3858424ba9

-- Sol generated from Algebra/WhichFactorWallInvariant.lean
import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
import Theorems.Thm_WhichFactorWall_binEntropy_sub_ge
/-
# The which-factor wall as a cross-population invariant: how much does it really pin down?

This file continues `Speculative.AutoResearch.TraceBatteryWall`
(`TraceBattery.binary_wall_inversion`), which shows that a *binary* capacity
("wall") value determines the class imbalance of a two-valued statistic
**uniquely** on the balanced side `[0, 1/2]`.  Uniqueness, however, is a
qualitative statement.  The research question of this cycle is quantitative:

> if two independent populations report walls that agree to within `ε`,
> how close are their class imbalances?

The mission proposal was:

  `|binEntropy p - binEntropy q| ≥ c(δ) |p - q|` on `[δ, 1/2]`,
  with `c(δ) = log ((1-δ)/δ)`.

**This is false**, and `binEntropy_conjectured_lower_bound_false` refutes it with
an exact counterexample (`δ = q = 1/4`, `p = 1/2`), where the failure reduces to
`log 16 ≤ log 27`.  The reason is structural: `c(δ)` is the *supremum* of
`|binEntropy'|` on `[δ, 1/2]`, not its infimum, so it controls the Lipschitz
(upper) bound, while the true inverse bound must be governed by the derivative
at the endpoint *closest to* `1/2`.

What survives, and is proved here with zero sorries:

* `binEntropy_sub_ge` — the sharp mean-value lower bound
  `(q - p) * (log (1-q) - log q) ≤ binEntropy q - binEntropy p` for
  `0 ≤ p ≤ q ≤ 1/2` (including the boundary case `p = 0`).
* `binEntropy_lipschitz` — the true version of the proposed inequality, with the
  inequality reversed: `|binEntropy p - binEntropy q| ≤ c(δ) |p - q|` on
  `[δ, 1-δ]`.
* `imbalance_dist_le` / `imbalance_dist_le_div` — the corrected **cross-population
  stability theorem**: imbalances in `[0, 1/2 - η]` whose walls agree within `ε`
  agree within `ε / log ((1/2+η)/(1/2-η))`.
* `binary_wall_stability` — the same statement at the level of two binary
  statistics on two different finite populations, via the empirical entropy `H`.
* `log_two_sub_binEntropy_le_sq` — `log 2 - binEntropy (1/2 - t) ≤ 4 t²`, and
  `no_uniform_inversion_constant`: **no** constant inverts the wall near `1/2`.
  So the guard `η > 0` is not an artefact: the wall genuinely loses all
  resolution at balance, at a quadratic rate.
* `wall_imbalance_bracket` — the reported wall `0.4677` bits is a falsifiable
  claim about the split: the unique minority fraction in `[0, 1/2]` realising it
  lies strictly between `1/12` and `1/9` (i.e. between 8.34% and 11.11%),
  consistent with the reported 9.96% and inconsistent with, say, a 5% or a 15%
  split.

Because the catalog module `Combinatorics.TraceBatteryEntropy` carrying the
empirical-entropy definitions is not present in this snapshot, the small
population layer (`img`, `cnt`, `H`, `H_two_values`) is restated here in the
open `WhichFactorWall`,
self-contained and compiles on its own.
-/

open WhichFactorWall

open Real Set

/-! ## 1.  Mean-value machinery for `Real.binEntropy`

`binEntropy` is differentiable away from `{0,1}` with derivative
`log (1-x) - log x` (Mathlib's `Real.deriv_binEntropy`).  We turn one-sided
bounds on that derivative into slope bounds by monotonicity of an auxiliary
function; this is the mean value theorem in the form we need. -/







/-! ## 2.  Refutation of the proposed inverse bound -/


/-! ## 3.  Corrected cross-population stability -/



/-! ## 4.  Why the guard `η > 0` cannot be dropped: quadratic degeneracy at balance -/



/-! ## 5.  Population layer: empirical entropy of a two-valued statistic

These are the definitions of the catalog's trace-battery entropy module,
restated so that this file is self-contained. -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α : Type*}




variable [DecidableEq α]






/-! ## 6.  The reported wall `0.4677` bits as a falsifiable claim about the split -/













theorem solution{η p q : ℝ} (hη : 0 < η) (hη2 : η < 2⁻¹)
    (hp : p ∈ Icc (0 : ℝ) (2⁻¹ - η)) (hq : q ∈ Icc (0 : ℝ) (2⁻¹ - η)) :
    (log (2⁻¹ + η) - log (2⁻¹ - η)) * |p - q| ≤ |binEntropy p - binEntropy q| := by
  have key : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) (2⁻¹ - η) → b ∈ Icc (0 : ℝ) (2⁻¹ - η) → a ≤ b →
      (log (2⁻¹ + η) - log (2⁻¹ - η)) * |a - b| ≤ |binEntropy a - binEntropy b| := by
    intro a b ha hb hab
    rcases eq_or_lt_of_le hb.1 with hb0 | hb0
    · have : a = b := le_antisymm hab (hb0 ▸ ha.1)
      simp [this]
    · have hb2 : b ≤ 2⁻¹ - η := hb.2
      have hslope : log (2⁻¹ + η) - log (2⁻¹ - η) ≤ log (1 - b) - log b := by
        have h1 : log (2⁻¹ + η) ≤ log (1 - b) := Real.log_le_log (by linarith) (by linarith)
        have h2 : log b ≤ log (2⁻¹ - η) := Real.log_le_log hb0 hb2
        linarith
      have hmvt := binEntropy_sub_ge ha.1 hab (by linarith)
      have hnn : 0 ≤ b - a := by linarith
      have h1 : (log (2⁻¹ + η) - log (2⁻¹ - η)) * (b - a) ≤ binEntropy b - binEntropy a := by
        nlinarith [hmvt, hslope, hnn]
      have h2 : 0 ≤ binEntropy b - binEntropy a := by
        have hc : 0 ≤ log (2⁻¹ + η) - log (2⁻¹ - η) := by
          have := Real.log_le_log (show (0:ℝ) < 2⁻¹ - η by linarith)
            (show (2:ℝ)⁻¹ - η ≤ 2⁻¹ + η by linarith)
          linarith
        nlinarith [h1, hc, hnn]
      rw [abs_of_nonpos (by linarith : a - b ≤ 0), abs_of_nonpos (by linarith :
        binEntropy a - binEntropy b ≤ 0)]
      linarith
  rcases le_total p q with h | h
  · exact key p q hp hq h
  · rw [abs_sub_comm, abs_sub_comm (binEntropy p)]; exact key q p hq hp h
