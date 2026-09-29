-- Prove2me | solution 1 for ProfileForm.windowMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:12:29.387839+00:00
-- url     : https://prove2.me/submissions/b7e42a70-10ad-474f-93fd-3abafab06e59

-- Sol generated from NumberTheory/ProfileFormExponentThreshold.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormExponentThreshold
import Definitions.Def_NumberTheory_ProfileFormPowerLaw

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
theorem solution{b X : ℝ} (hb : b ≠ 1) (hX : 0 ≤ X) :
    windowMass b X = ((1 + X) ^ (1 - b) - 1) / (1 - b) := by
  have hb' : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) X,
      HasDerivAt (fun x : ℝ => (1 + x) ^ (1 - b) / (1 - b)) ((1 + x) ^ (-b)) x := by
    intro x hx
    have hx0 : 0 ≤ x := by
      rcases Set.mem_uIcc.mp hx with h | h
      · exact h.1
      · linarith [h.1]
    have hne : (1 : ℝ) + x ≠ 0 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h2 := (h1.rpow_const (p := 1 - b) (Or.inl hne)).div_const (1 - b)
    have hsimp : 1 * (1 - b) * (1 + x) ^ (1 - b - 1) / (1 - b) = (1 + x) ^ (-b) := by
      rw [show (1 : ℝ) - b - 1 = -b by ring]
      field_simp
    rwa [hsimp] at h2
  have hint : IntervalIntegrable (fun x : ℝ => (1 + x) ^ (-b)) MeasureTheory.volume 0 X := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : 0 ≤ x := by
      rcases Set.mem_uIcc.mp hx with h | h
      · exact h.1
      · linarith [h.1]
    have hpos : (0:ℝ) < 1 + x := by linarith
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hpos))).continuousWithinAt.comp
      (by fun_prop : ContinuousWithinAt (fun x : ℝ => 1 + x) (Set.uIcc 0 X) x)
      (fun y _ => Set.mem_univ _)
  rw [windowMass, integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [add_zero, Real.one_rpow]
  ring
