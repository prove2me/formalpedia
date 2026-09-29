-- Prove2me | solution 1 for PrimeFractal.eventually_log_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:11:49.335211+00:00
-- url     : https://prove2.me/submissions/a90e0216-9f5a-48d6-9124-620902707857

-- Sol generated from NumberTheory/PrimeFractalBoxDimension.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff

/-!
# The box-counting dimension of the prime fractal is exactly `1`

`NumberTheory.PrimeFractalHausdorff` shows that the Hausdorff dimension of the
prime fractal `{1 / log p : p prime} ⊆ ℝ` is `0`, refuting the mission
conjecture.  Here we prove the *positive* half of the story: the notion that
actually sees the conjectured value is the **box-counting (Minkowski)
dimension**, and for the prime fractal it equals `1` on the nose.

At scale `1/m` we count the boxes `[k/m, (k+1)/m)` that meet the prime fractal,
i.e. the cardinality `boxCount m` of the set of values `⌊m / log p⌋` over primes
`p`.  The two halves are:

* `boxCount_le` : `boxCount m ≤ 2m + 1` — a trivial upper bound valid for any
  subset of an interval, which is what forces the dimension to be `≤ 1`.  In
  particular *no* configuration of primes — twin primes included — can produce
  a dimension `1 + ε` with `ε > 0`.
* `eventually_boxCount_ge` : `boxCount m ≥ m / (16 (log m)^4)`.  This is the
  arithmetic input: it uses the Chebyshev-type lower bound
  `PrimeFractal.le_primeCounting_mul_log` together with the observation that
  `p ↦ ⌊m / log p⌋` is injective on primes `p ≤ Y` as soon as
  `2 Y (log Y)^2 ≤ m` (primes below `Y` are spread more than `1/m` apart in the
  `d`-metric).

Together they give `tendsto_boxCount_log_div`: `log (boxCount m) / log m → 1`,
hence `upperBoxDim = lowerBoxDim = 1` (`upperBoxDim_eq_one`,
`lowerBoxDim_eq_one`), while the Hausdorff dimension is `0`
(`dimH_lt_boxDim`).  The prime fractal is therefore a *dimension-irregular*
set: box and Hausdorff dimensions disagree maximally.
-/

open PrimeFractal

open Filter Topology




/-! ### Elementary bounds -/







/-! ### Separation of primes in the `d`-metric -/




/-! ### From Chebyshev to a lower bound on the box count -/



/-! ### Asymptotics -/














open PrimeFractal in
theorem solution{C : ℝ} (hC : 0 < C) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, C * (Real.log m) ^ k ≤ (m : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in atTop, C * (Real.log x) ^ k ≤ x := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := k)).def (c := 1 / C) (by positivity)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hidx : (0 : ℝ) ≤ id x := by simpa using (by linarith : (0 : ℝ) ≤ x)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg hidx] at hx
    have : C * (Real.log x ^ k) ≤ C * ((1 / C) * x) := by
      exact mul_le_mul_of_nonneg_left hx (le_of_lt hC)
    calc C * Real.log x ^ k ≤ C * ((1 / C) * x) := this
      _ = x := by field_simp
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal
