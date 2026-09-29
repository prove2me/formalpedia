-- Prove2me | solution 1 for ProfileForm.tailResidual_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:59:42.999214+00:00
-- url     : https://prove2.me/submissions/1510aa7d-a89a-4010-bd28-21efe9332b01

-- Sol generated from NumberTheory/ProfileFormHumpLocation.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormHumpLocation
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Theorems.Thm_ProfileForm_tailResidual_hasDerivAt

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






theorem tailResidual_deriv (b : ℝ) {x : ℝ} (hx : -1 < x) :
    deriv (tailResidual b) x = (1 + x) ^ (-b - 1) * (1 - (b - 1) * x) :=
  (tailResidual_hasDerivAt b hx).deriv

theorem tailResidual_continuousOn (b : ℝ) : ContinuousOn (tailResidual b) (Ici (0:ℝ)) := by
  intro x hx
  have h1 : (0:ℝ) < 1 + x := by simp only [mem_Ici] at hx; linarith
  refine ContinuousAt.continuousWithinAt (ContinuousAt.mul continuousAt_id ?_)
  exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt h1))).comp (by fun_prop)









/-! ### Transfer to the true uniform-mixture residual -/










open ProfileForm in
theorem solution{b : ℝ} (hb : 1 < b) :
    StrictMonoOn (tailResidual b) (Icc 0 (humpLocation b)) := by
  have hb1 : (0:ℝ) < b - 1 := by linarith
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    ((tailResidual_continuousOn b).mono (Icc_subset_Ici_self)) ?_
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨hx0, hx1⟩ := hx
  have hxm : -1 < x := by linarith
  rw [tailResidual_deriv b hxm]
  have hpos : (0:ℝ) < (1 + x) ^ (-b - 1) := Real.rpow_pos_of_pos (by linarith) _
  have hlt : (b - 1) * x < 1 := by
    have hx1' : x < 1 / (b - 1) := by simpa [humpLocation] using hx1
    have := (lt_div_iff₀ hb1).mp hx1'
    linarith [this]
  exact mul_pos hpos (by linarith)
