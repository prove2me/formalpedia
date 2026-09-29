-- Prove2me | solution 1 for SpectralNetworkRobustness.connectivity_alone_no_robustness_radius
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:55:40.182456+00:00
-- url     : https://prove2.me/submissions/4a16e76b-b6a9-4c9f-bb74-80964df4ca7e

-- Sol generated from Geometry/SpectralNetworkRobustness.lean
import Mathlib
import Definitions.Def_Geometry_SpectralNetworkRobustness

/-!
# Spectral graph control and certified robustness

This file isolates a precise, non-vacuous version of the proposed connection.
A graph spectral gap controls the squared variation of an internal computation
state; a Lipschitz readout then converts that control into an end-to-end
Lipschitz bound, which yields a certified classification radius.

It also formalizes two contrarian negative results: algebraic connectivity alone
cannot control either a network's Lipschitz constant or its robustness radius.
A gain bound and a positive output margin are both indispensable.
-/

open SpectralNetworkRobustness














open SpectralNetworkRobustness in
theorem solution    (R : ℝ) (hR : 0 < R) :
    ∃ f : ℝ → ℝ, 0 < f 0 ∧ LipschitzBound f 1 ∧
      ¬ CertifiedPositive f 0 R := by
  use fun x => R / 2 - x
  refine ⟨by linarith, ?_, ?_⟩
  · intro x y
    show |R / 2 - x - (R / 2 - y)| ≤ 1 * |x - y|
    have : R / 2 - x - (R / 2 - y) = y - x := by ring
    rw [this]
    simp [abs_sub_comm]
  · simp only [CertifiedPositive, not_forall, not_lt, exists_prop]
    use R / 2
    constructor
    · rw [abs_of_pos] <;> linarith
    · norm_num
