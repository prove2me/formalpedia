-- Prove2me | solution 1 for ProofRegimeMixture.mixedTail_ratio_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:11:25.309061+00:00
-- url     : https://prove2.me/submissions/57bfa09b-0996-4170-ba4f-d585e4f2928b

-- Sol generated from Shared/ProofRegimeMixturePowerLaw.lean
import Mathlib
import Definitions.Def_Shared_ProofRegimeMixturePowerLaw

/-!
# Power Laws from Mixtures of Geometric Proof Regimes

`Shared.ProofSpacePhaseTransition` shows that a *single* proof regime of fixed
entropy has a length distribution with a constant successive ratio
(`CountedProofSpace.geometric_length_ratio_is_entropy`), which rules out a raw
power law for theorem lengths inside one homogeneous proof space.

Here we test the replacement hypothesis: a genuine power law can only come from
*heterogeneity across regimes*.  Model a family of proof regimes by their
entropy parameter `s`, the regime of parameter `s` having geometric length tail
`exp (-s x)`, and mix uniformly over `s ∈ [0,1]`:

  `mixedTail x = ∫ s in 0..1, exp (-(x * s))`.

Results:

* `regimeTail_ratio` — inside one regime the successive ratio is the constant
  `exp (-s)` (the catalog's constant-ratio law, in tail form);
* `mixedTail_eq` — the mixture has the *exact* closed form `(1 - exp (-x)) / x`;
* `mixedTail_power_bounds` — hence `(1 - e⁻¹)/x ≤ mixedTail x ≤ 1/x`: an exact
  power law of exponent one, with explicit constants;
* `mixedTail_regularly_varying` — `x · mixedTail x → 1`, i.e. the tail is
  regularly varying of index `-1`;
* `mixedTail_ratio_tendsto_one` — the successive ratio tends to `1`, not to a
  constant `< 1`: the mixture is *not* geometric;
* `mixedTail_not_geometric` — no geometric bound `C a ^ n` with `a < 1` can
  dominate the mixed tail.

So the scale mixture is exactly the mechanism that converts constant-ratio
regimes into a power law, and the resulting exponent is dictated by the mixing
law near zero entropy.
-/

open ProofRegimeMixture

open Filter Topology intervalIntegral




/-- **Closed form of the mixed tail.** -/
theorem mixedTail_eq (x : ℝ) (hx : 0 < x) :
    mixedTail x = (1 - Real.exp (-x)) / x := by
  unfold mixedTail
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.exp (-t)) (ne_of_gt hx)]
  simp [intervalIntegral.integral_comp_neg (fun t => Real.exp t)]
  field_simp





-- !-- Lab Notes -- !--
-- Hypothesis: (1) One regime of fixed entropy has a constant successive ratio;
-- (2) a scale mixture over the entropy parameter produces a genuine power law;
-- (3) the mixed successive ratio tends to 1, falsifying the geometric model;
-- (4) no geometric bound dominates the mixed tail.  All four survive.
-- Experiment: The uniform mixture was integrated exactly, giving
-- (1 - exp(-x))/x.  Numerically x * mixedTail x is 0.632, 0.865, 0.950, 0.993,
-- 0.99996 at x = 1, 2, 3, 5, 10, and the successive ratios are 0.684, 0.733,
-- 0.837, 0.909, 0.980, 0.995 at n = 1, 2, 5, 10, 50, 200: increasing to 1 rather
-- than sitting at a constant exp(-s) < 1.
-- Analysis: The power law comes entirely from the mixing law near zero entropy;
-- the small-s regimes have almost flat tails and dominate at large lengths.  The
-- exponent 1 is the index of the uniform mixing law, matching the heuristic that
-- a mixing density proportional to s^(alpha-1) should give index alpha.
-- Critique: Only the uniform mixing law is treated exactly; a general alpha
-- requires incomplete-Gamma asymptotics, and the Tauberian converse is not
-- attempted.  The model is a tail model for lengths, not a derivation from any
-- specific calculus.
-- Synthesis: Heterogeneity across proof regimes, and not any single entropy, is
-- what can produce a power law; the catalog's constant-ratio law is recovered
-- here as the degenerate one-regime case.


open ProofRegimeMixture in
theorem solution:
    Tendsto (fun n : ℕ => mixedTail (n + 1) / mixedTail n) atTop (𝓝 1) := by
  have hexpn : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hexpn1 : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    exact h
  have hnum : Tendsto (fun n : ℕ => (1 - Real.exp (-((n : ℝ) + 1)))) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) - Real.exp (-((n : ℝ) + 1))) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hexpn1
    rwa [sub_zero] at h
  have hden : Tendsto (fun n : ℕ => (1 - Real.exp (-(n : ℝ)))) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) - Real.exp (-(n : ℝ))) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hexpn
    rwa [sub_zero] at h
  have hfrac : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hlim : Tendsto (fun n : ℕ =>
      ((1 - Real.exp (-((n : ℝ) + 1))) / (1 - Real.exp (-(n : ℝ)))) * ((n : ℝ) / ((n : ℝ) + 1)))
      atTop (𝓝 1) := by
    have h := (hnum.div hden one_ne_zero).mul hfrac
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hd : (0 : ℝ) < 1 - Real.exp (-(n : ℝ)) := by
    have : Real.exp (-(n : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  rw [mixedTail_eq _ hn1, mixedTail_eq _ hnpos]
  field_simp
