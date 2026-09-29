-- Prove2me | solution 1 for Spike.Quantile.quantile_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:13:32.96317+00:00
-- url     : https://prove2.me/submissions/f8f6104a-c071-4b2c-ad24-a3a3dc96fb91

-- Sol generated from Probability/SpikeQuantileLimitLaw.lean
import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry
import Definitions.Def_Probability_SpikeQuantileIdentity
import Definitions.Def_Probability_SpikeQuantileLimitLaw
import Theorems.Thm_Spike_Quantile_quantile_law_error

/-!
# The continuum quantile law of the window residue

`Catalog/Probability/SpikeQuantileIdentity.lean` proves the exact discrete
quantile identity

`#{ j ∈ W N : residue N j ≤ x } = min (3 isqrt N) (isqrt (N + x)) - isqrt N`.

This file closes the remaining, *asymptotic* half of future direction 1: the
limit law of the rescaled residue `v / s²` under the uniform position law on the
window.  Everything is proved with an explicit, non-asymptotic error term, so the
limit statement is a corollary rather than the primitive result.

Main results (`Spike.Quantile`):

* `card_sublevel_sq` : on a perfect-square modulus `N = M²` (where the integer
  and real square roots agree, so no rounding of the anchor occurs) the sublevel
  count is exactly `isqrt (M² + x) - M` as long as `x ≤ 8 M²`, i.e. as long as
  the threshold stays inside the window;
* `quantile_law_error` : the **Kolmogorov distance bound**
  `| F_M(x) - (√(1 + x/M²) - 1)/2 | ≤ 1/(2M)`
  where `F_M(x)` is the empirical fraction of window positions with residue at
  most `x`.  The limit c.d.f. `y ↦ (√(1+y) - 1)/2` is precisely the law of
  `(1 + 2U)² - 1` for `U` uniform on `[0,1]`, which is the conjectured law;
* `quantile_tendsto` : consequently, for every level `y ∈ [0,8]` the empirical
  fraction below `y M²` converges to `(√(1+y) - 1)/2`;
* `decile_law_exact` : at the round-85 decile level `y = 11/25` the limit law
  returns exactly `1/10`, and on the divisible moduli `N = (5m)²` the empirical
  fraction *equals* `1/10` with no error at all — the decile statistic and the
  magnitude statistic agree exactly, not just in the limit.

Interpretation: a first-decile analysis on this window is a `v ≤ 0.44 s²`
analysis with an error of at most one position, at every scale.  There is no
asymptotic regime in which the positional cut carries information beyond the
magnitude cut.
-/

open Spike.Quantile

open Spike Filter

/-! ### Comparison of the integer and real square roots -/




/-! ### The exact sublevel count on a perfect-square modulus -/




/-! ### The limit law, with an explicit error term -/






/-! ### The decile point: the limit law is attained exactly -/




open Spike.Quantile in
theorem solution(y : ℝ) (hy : 0 ≤ y) (hy8 : y ≤ 8) :
    Tendsto (fun M : ℕ => empFrac M ⌊y * (M : ℝ) ^ 2⌋₊) atTop (nhds (limitCDF y)) := by
  set u : ℕ → ℝ := fun M => ((⌊y * (M : ℝ) ^ 2⌋₊ : ℕ) : ℝ) / (M : ℝ) ^ 2 with hu_def
  -- the rescaled thresholds converge to `y`
  have hufloor : ∀ M : ℕ, 0 < M → |u M - y| ≤ 1 / (M : ℝ) := by
    intro M hM
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
    have h1 : ((⌊y * (M : ℝ) ^ 2⌋₊ : ℕ) : ℝ) ≤ y * (M : ℝ) ^ 2 :=
      Nat.floor_le (by positivity)
    have h2 : y * (M : ℝ) ^ 2 - 1 < ((⌊y * (M : ℝ) ^ 2⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (y * (M : ℝ) ^ 2)
      linarith
    have hMle : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have heq : u M - y = (((⌊y * (M : ℝ) ^ 2⌋₊ : ℕ) : ℝ) - y * (M : ℝ) ^ 2) / (M : ℝ) ^ 2 := by
      rw [hu_def]; field_simp
    have hnum : |((⌊y * (M : ℝ) ^ 2⌋₊ : ℕ) : ℝ) - y * (M : ℝ) ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    rw [heq, abs_div, abs_of_pos hM2]
    calc |((⌊y * (M : ℝ) ^ 2⌋₊ : ℕ) : ℝ) - y * (M : ℝ) ^ 2| / (M : ℝ) ^ 2
        ≤ 1 / (M : ℝ) ^ 2 := by gcongr
      _ ≤ 1 / (M : ℝ) := by
          apply one_div_le_one_div_of_le hM'
          nlinarith
  have hu : Tendsto u atTop (nhds y) := by
    have hbound : ∀ᶠ M : ℕ in atTop, ‖u M - y‖ ≤ 1 / (M : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with M hM
      simpa [Real.norm_eq_abs] using hufloor M hM
    have hzero : Tendsto (fun M : ℕ => 1 / (M : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have := squeeze_zero_norm' hbound hzero
    simpa using this.add (tendsto_const_nhds (x := y) (f := atTop (α := ℕ)))
  -- the limit c.d.f. is continuous
  have hcont : Continuous limitCDF := by
    unfold limitCDF
    fun_prop
  have hg : Tendsto (fun M : ℕ => limitCDF (u M)) atTop (nhds (limitCDF y)) :=
    (hcont.tendsto y).comp hu
  -- the difference vanishes
  have hdiff : Tendsto (fun M : ℕ => empFrac M ⌊y * (M : ℝ) ^ 2⌋₊ - limitCDF (u M))
      atTop (nhds 0) := by
    have hbound : ∀ᶠ M : ℕ in atTop,
        ‖empFrac M ⌊y * (M : ℝ) ^ 2⌋₊ - limitCDF (u M)‖ ≤ 1 / (M : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with M hM
      have hM' : (0 : ℝ) < M := by exact_mod_cast hM
      have hx : ⌊y * (M : ℝ) ^ 2⌋₊ ≤ 8 * M ^ 2 := by
        have h1 : y * (M : ℝ) ^ 2 ≤ ((8 * M ^ 2 : ℕ) : ℝ) := by
          push_cast
          nlinarith [sq_nonneg ((M : ℝ))]
        simpa using Nat.floor_le_of_le h1
      have h := quantile_law_error M ⌊y * (M : ℝ) ^ 2⌋₊ hM hx
      have hhalf : 1 / (2 * (M : ℝ)) ≤ 1 / (M : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hM'
        linarith
      simpa [Real.norm_eq_abs, hu_def] using h.trans hhalf
    exact squeeze_zero_norm' hbound tendsto_one_div_atTop_nhds_zero_nat
  simpa using hdiff.add hg
