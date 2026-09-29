-- Prove2me | solution 1 for PrimeFractal.tendsto_boxCount_log_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:29.391545+00:00
-- url     : https://prove2.me/submissions/fc966e56-72fd-4483-b8b2-cc06858cea6e

-- Sol generated from NumberTheory/PrimeFractalBoxDimension.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff
import Theorems.Thm_PrimeFractal_boxIndex_le
import Theorems.Thm_PrimeFractal_eventually_boxCount_ge
import Theorems.Thm_PrimeFractal_eventually_two_le_log
import Theorems.Thm_PrimeFractal_one_le_boxCount
import Theorems.Thm_PrimeFractal_tendsto_inv_log
import Theorems.Thm_PrimeFractal_tendsto_log_log_div_log

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



theorem occupiedBoxes_subset (m : ℕ) : occupiedBoxes m ⊆ ↑(Finset.range (2 * m + 1)) := by
  rintro k ⟨p, hp, rfl⟩
  simp only [Finset.coe_range, Set.mem_Iio]
  exact Nat.lt_succ_of_le (boxIndex_le m p hp.two_le)


/-- The trivial upper bound on the box count: at scale `1/m` the prime fractal, which
lives inside `[0, 2]`, can meet at most `2m + 1` boxes. -/
theorem boxCount_le (m : ℕ) : boxCount m ≤ 2 * m + 1 := by
  have h := Set.ncard_le_ncard (occupiedBoxes_subset m) (Finset.range (2 * m + 1)).finite_toSet
  simpa [boxCount, Set.ncard_coe_finset] using h


/-! ### Separation of primes in the `d`-metric -/




/-! ### From Chebyshev to a lower bound on the box count -/



/-! ### Asymptotics -/














open PrimeFractal in
theorem solution:
    Tendsto (fun m : ℕ => Real.log (boxCount m) / Real.log m) atTop (𝓝 1) := by
  have hupper : ∀ᶠ m : ℕ in atTop,
      Real.log (boxCount m) / Real.log m ≤ 1 + Real.log 3 * (1 / Real.log m) := by
    filter_upwards [eventually_two_le_log, eventually_ge_atTop 1] with m hL2 hm1
    have hL0 : 0 < Real.log m := by linarith
    have hm0 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hb : (boxCount m : ℝ) ≤ 3 * (m : ℝ) := by
      have := boxCount_le m
      have : ((boxCount m : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    have hb0 : (0 : ℝ) < (boxCount m : ℝ) := by
      have := one_le_boxCount m
      exact_mod_cast lt_of_lt_of_le zero_lt_one (by exact_mod_cast this)
    have hlog : Real.log (boxCount m) ≤ Real.log 3 + Real.log m := by
      have := Real.log_le_log hb0 hb
      rwa [Real.log_mul (by norm_num) (by linarith)] at this
    rw [div_le_iff₀ hL0]
    field_simp
    linarith
  have hlower : ∀ᶠ m : ℕ in atTop,
      1 - (Real.log 16 * (1 / Real.log m) + 4 * (Real.log (Real.log m) / Real.log m))
        ≤ Real.log (boxCount m) / Real.log m := by
    filter_upwards [eventually_boxCount_ge, eventually_two_le_log, eventually_ge_atTop 1]
      with m hge hL2 hm1
    have hL0 : 0 < Real.log m := by linarith
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hpos : (0 : ℝ) < (m : ℝ) / (16 * (Real.log m) ^ 4) := by positivity
    have hlog := Real.log_le_log hpos hge
    have hexp : Real.log ((m : ℝ) / (16 * (Real.log m) ^ 4))
        = Real.log m - Real.log 16 - 4 * Real.log (Real.log m) := by
      rw [Real.log_div (ne_of_gt hm0) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [hexp] at hlog
    rw [le_div_iff₀ hL0]
    field_simp
    linarith
  have h1 : Tendsto (fun m : ℕ => 1 + Real.log 3 * (1 / Real.log m)) atTop (𝓝 1) := by
    have := (tendsto_inv_log.const_mul (Real.log 3))
    simpa using tendsto_const_nhds.add this
  have h2 : Tendsto (fun m : ℕ =>
      1 - (Real.log 16 * (1 / Real.log m) + 4 * (Real.log (Real.log m) / Real.log m)))
      atTop (𝓝 1) := by
    have ha := tendsto_inv_log.const_mul (Real.log 16)
    have hb := tendsto_log_log_div_log.const_mul (4 : ℝ)
    have := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)) |>.sub (ha.add hb)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 hlower hupper
