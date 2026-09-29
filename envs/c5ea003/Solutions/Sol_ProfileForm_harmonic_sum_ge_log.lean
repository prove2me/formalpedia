-- Prove2me | solution 1 for ProfileForm.harmonic_sum_ge_log
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:31:17.184576+00:00
-- url     : https://prove2.me/submissions/60ffcc48-a22d-4042-b79c-dbf370854482

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
theorem solution(n : ℕ) :
    Real.log (n + 1) ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : (0:ℝ) < n + 1 := by positivity
      have hstep : Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1) ≤ 1 / (n + 1) := by
        have hratio : Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) ≤ ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hsplit : Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1))
            = Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) :=
          Real.log_div (by positivity) (by positivity)
        have harith : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
          field_simp
          ring
        rw [hsplit, harith] at hratio
        have : ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 := by ring
        rw [this]
        exact hratio
      have hrec : ∑ j ∈ Finset.range (n + 1), (1 : ℝ) / (j + 1)
          = (∑ j ∈ Finset.range n, (1 : ℝ) / (j + 1)) + 1 / ((n : ℝ) + 1) := by
        rw [Finset.sum_range_succ]
      rw [hrec]
      push_cast
      linarith
