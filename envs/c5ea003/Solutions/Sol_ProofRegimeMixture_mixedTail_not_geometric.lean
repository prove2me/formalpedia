-- Prove2me | solution 1 for ProofRegimeMixture.mixedTail_not_geometric
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:11:24.684718+00:00
-- url     : https://prove2.me/submissions/a59a8d72-e9d6-4eab-b8c7-dc812393cdee

-- Sol generated from Shared/ProofRegimeMixturePowerLaw.lean
import Mathlib
import Definitions.Def_Shared_ProofRegimeMixturePowerLaw
import Theorems.Thm_ProofRegimeMixture_mixedTail_power_bounds

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
theorem solution(a C : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ¬ (∀ n : ℕ, 1 ≤ n → mixedTail n ≤ C * a ^ n) := by
  intro hcon
  have hgeo : Tendsto (fun n : ℕ => C * ((n : ℝ) * a ^ n)) atTop (𝓝 (C * 0)) := by
    refine tendsto_const_nhds.mul ?_
    exact tendsto_self_mul_const_pow_of_lt_one ha0 ha1
  rw [mul_zero] at hgeo
  have hpos : 0 < 1 - Real.exp (-1) := by
    have : Real.exp (-1 : ℝ) < 1 := by
      rw [Real.exp_lt_one_iff]; norm_num
    linarith
  obtain ⟨N, hN⟩ := (hgeo.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
  have hN1 := hN (max N 1) (le_max_left _ _)
  have hn1 : 1 ≤ max N 1 := le_max_right _ _
  have hnpos : (0 : ℝ) < (max N 1 : ℕ) := by
    have : (1 : ℕ) ≤ max N 1 := hn1
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
  have hlow := (mixedTail_power_bounds ((max N 1 : ℕ) : ℝ) (by exact_mod_cast hn1)).1
  have hup := hcon (max N 1) hn1
  have hchain : (1 - Real.exp (-1)) / ((max N 1 : ℕ) : ℝ) ≤ C * a ^ (max N 1) :=
    le_trans hlow hup
  rw [div_le_iff₀ hnpos] at hchain
  nlinarith [hN1]
