-- Prove2me | solution 1 for ProfileForm.windowMass_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:15:41.663946+00:00
-- url     : https://prove2.me/submissions/755b9db4-39cd-4826-a6fa-e59be46e491a

-- Sol generated from NumberTheory/ProfileFormExponentThreshold.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormExponentThreshold
import Definitions.Def_NumberTheory_ProfileFormPowerLaw
import Theorems.Thm_ProfileForm_windowMass_eq
import Theorems.Thm_ProfileForm_windowMass_eq_log

/-!
# Profile form IV: the exponent-one threshold that the bootstrap straddles

Context (experiment 579, paper 229).  The fitted exponent of the positional
profile is `b ≈ 1.104` with cluster-bootstrap interval `b ∈ [0.991, 1.218]`.
That interval contains `1`, and `b = 1` is not an arbitrary number: it is the
exact threshold at which the total window mass of the profile changes from
divergent to finite.  Here we prove the threshold and then prove that the
measured interval genuinely straddles it, i.e. the experiment as it stands
cannot decide the qualitative question.

* `windowMass_eq` — closed form `∫₀^X (1+x)^(-b) dx = ((1+X)^(1-b) - 1)/(1-b)`
  for `b ≠ 1`;
* `windowMass_eq_log` — the harmonic case `b = 1` gives exactly `log (1+X)`;
* `windowMass_tendsto_finite` — for `b > 1` the total mass converges to
  `1/(b-1)`;
* `windowMass_tendsto_atTop` — for `b ≤ 1` it diverges;
* `exponent_bootstrap_straddles_threshold` — inside the bootstrap interval
  `[0.991, 1.218]` both behaviours occur;
* `harmonic_sum_ge_log` — the discrete counterpart: the harmonic hit counts of
  the critical profile `b = 1` dominate `log (n+1)`, so the divergence is
  visible already at the level of counted hits.
-/

open ProfileForm

open Real Filter Topology intervalIntegral







/-! ## The discrete counterpart -/



open ProfileForm in
theorem solution{b : ℝ} (hb : b ≤ 1) :
    Tendsto (windowMass b) atTop atTop := by
  have hshift : Tendsto (fun X : ℝ => 1 + X) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_id
  rcases eq_or_lt_of_le hb with h | h
  · subst h
    have heq : ∀ᶠ X : ℝ in atTop, windowMass 1 X = Real.log (1 + X) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX using windowMass_eq_log hX
    rw [tendsto_congr' heq]
    exact Real.tendsto_log_atTop.comp hshift
  · have hb' : b ≠ 1 := ne_of_lt h
    have heq : ∀ᶠ X : ℝ in atTop, windowMass b X = ((1 + X) ^ (1 - b) - 1) / (1 - b) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX using windowMass_eq hb' hX
    rw [tendsto_congr' heq]
    have hrpow : Tendsto (fun X : ℝ => (1 + X) ^ (1 - b)) atTop atTop := by
      have h0 : Tendsto (fun y : ℝ => y ^ (1 - b)) atTop atTop :=
        tendsto_rpow_atTop (by linarith)
      exact h0.comp hshift
    have hpos : (0:ℝ) < 1 - b := by linarith
    exact ((hrpow.atTop_add tendsto_const_nhds).atTop_div_const hpos)
