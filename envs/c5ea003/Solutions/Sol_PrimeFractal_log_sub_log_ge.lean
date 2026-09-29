-- Prove2me | solution 1 for PrimeFractal.log_sub_log_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:06:56.757254+00:00
-- url     : https://prove2.me/submissions/1bfafbc4-9a0f-4263-a217-916e58da39bc

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
theorem solution{p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) :
    1 / (2 * (p : ℝ)) ≤ Real.log q - Real.log p := by
  have hP : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hQ : (p : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hpq
  set P : ℝ := (p : ℝ)
  set u : ℝ := 1 / (2 * P) with hu
  have hP0 : 0 < P := by linarith
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 4 := by
    rw [hu]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- `exp u ≤ 1 / (1 - u)`
  have hexp : (1 - u) * Real.exp u ≤ 1 := by
    have h := Real.add_one_le_exp (-u)
    rw [Real.exp_neg] at h
    have hpos : 0 < Real.exp u := Real.exp_pos u
    have h' : (1 - u) ≤ (Real.exp u)⁻¹ := by linarith
    calc (1 - u) * Real.exp u ≤ (Real.exp u)⁻¹ * Real.exp u := by nlinarith
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  -- hence `P * exp u ≤ Q`
  have hkey : P * Real.exp u ≤ (q : ℝ) := by
    have h1u : 0 < 1 - u := by linarith
    have hPQ : P ≤ (q : ℝ) * (1 - u) := by
      have hexpand : (q : ℝ) * (1 - u) = (q : ℝ) - (q : ℝ) * (1 / (2 * P)) := by
        rw [hu]; ring
      have hqu : (q : ℝ) * (1 / (2 * P)) ≤ (q : ℝ) - P := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        nlinarith [hQ, hP0]
      rw [hexpand]
      linarith
    nlinarith [Real.exp_pos u, hexp, hPQ, h1u]
  have hlog : Real.log (P * Real.exp u) ≤ Real.log q :=
    Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero u), Real.log_exp] at hlog
  linarith
