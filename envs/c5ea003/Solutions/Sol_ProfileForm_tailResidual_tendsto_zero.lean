-- Prove2me | solution 1 for ProfileForm.tailResidual_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:59:43.630502+00:00
-- url     : https://prove2.me/submissions/ff0c7353-534b-42de-86d5-1c36e2fe0b87

-- Sol generated from NumberTheory/ProfileFormHumpLocation.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormHumpLocation
import Definitions.Def_NumberTheory_ProfileFormResidualPeak

/-!
# Profile form VIII: the hump-location law

Stage-5 result of the cycle: we close the main open conjecture left by
`ProfileFormUniformMixturePeak` (Direction 1 of `FUTURE_DIRECTIONS.md`).

`ProfileFormUniformMixturePeak` exhibited a hump of the uniform-mixture residual
`R(x) = T(x)/M(x)` near `x ≈ 10` for the measured exponent `b = 11/10`, and
observed numerically that the hump sits near `1/(b-1) ≈ 9.6`.  Here that
observation becomes a theorem.

Write `T(x) = (1+x)^{-b}` and `M(x) = (1 - e^{-x})/x`.  Then exactly

  `R(x) = tailResidual b x / (1 - e^{-x})`,   `tailResidual b x = x (1+x)^{-b}`,

and the second factor tends to `1`, so the *shape* of `R` far from the origin is
governed by the elementary function `tailResidual`.  Its logarithmic derivative

  `d/dx log (x (1+x)^{-b}) = 1/x - b/(1+x) = (1 - (b-1)x) / (x(1+x))`

changes sign exactly once, at

  `x* = 1/(b-1)`,

for every `b > 1`.  This gives:

* `tailResidual_strictMonoOn` / `tailResidual_strictAntiOn` — strict increase on
  `[0, x*]`, strict decrease on `[x*, ∞)`;
* `tailResidual_unique_max` — `x*` is the *unique* maximiser on `[0,∞)`;
* `humpLocation_eleven_tenths` — the closed form `x* = 1/(b-1)` is exactly `10`
  at the measured exponent `b = 11/10`, matching the numerically located hump;
* `uniformResidual_hump_confined` — a quantitative transfer to the true
  residual: outside the set where `tailResidual` is within a factor
  `1 - e^{-x₀}` of its maximum, the true residual is strictly below its value at
  `x*`.  So the hump of `R` really is confined near `1/(b-1)`.

The law is a genuine *dichotomy* with the `b = 1` threshold of
`ProfileFormExponentThreshold`: for `b ≤ 1` no such maximiser exists,
`tailResidual` being then increasing throughout (`tailResidual_strictMono_of_le_one`).
So the same exponent-one threshold that decides the total window mass also
decides whether a hump exists at all — and the reported bootstrap interval
`[0.991, 1.218]` straddles it.
-/

open ProfileForm

open Set Filter Topology
















/-! ### Transfer to the true uniform-mixture residual -/










open ProfileForm in
theorem solution{b : ℝ} (hb : 1 < b) :
    Tendsto (tailResidual b) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => (1 + x) ^ (1 - b)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := b - 1) (by linarith)
    have hadd : Tendsto (fun x : ℝ => 1 + x) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 tendsto_id
    simpa [show -(b - 1) = 1 - b by ring] using h.comp hadd
  refine squeeze_zero' (Filter.eventually_ge_atTop (0:ℝ) |>.mono ?_)
    (Filter.eventually_ge_atTop (0:ℝ) |>.mono ?_) hpow
  · intro x hx
    have h1 : (0:ℝ) < 1 + x := by linarith
    exact mul_nonneg hx (Real.rpow_pos_of_pos h1 _).le
  · intro x hx
    have h1 : (0:ℝ) < 1 + x := by linarith
    have hle : x * (1 + x) ^ (-b) ≤ (1 + x) * (1 + x) ^ (-b) := by
      have := (Real.rpow_pos_of_pos h1 (-b)).le
      nlinarith [Real.rpow_pos_of_pos h1 (-b)]
    have heq : (1 + x) * (1 + x) ^ (-b) = (1 + x) ^ (1 - b) := by
      rw [show (1:ℝ) - b = 1 + (-b) by ring, Real.rpow_add h1, Real.rpow_one]
    simpa [tailResidual] using hle.trans heq.le
