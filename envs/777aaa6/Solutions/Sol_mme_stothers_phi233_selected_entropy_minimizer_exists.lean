-- Prove2me | solution 1 for mme_stothers_phi233_selected_entropy_minimizer_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:15:56.896274+00:00
-- url     : https://prove2.me/submissions/76b135db-d7d3-4885-850c-042e741a8339

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.RemainingFour

private noncomputable def phi233EntropyCost
    (sigma mu a : ℝ) : ℝ :=
  -2 * Real.negMulLog a -
    Real.negMulLog (sigma - 2 * a) -
    Real.negMulLog (mu - a) -
    Real.negMulLog (1 - sigma - mu + a)

private theorem continuous_phi233EntropyCost (sigma mu : ℝ) :
    Continuous (phi233EntropyCost sigma mu) := by
  unfold phi233EntropyCost
  fun_prop

/-- On every nonempty `phi_233` profile fiber, the logarithmic profile
product attains its minimum.  The interval coordinate is `a`, with the other
three frequencies recovered as `sigma - 2a`, `mu - a`, and
`1 - sigma - mu + a`. -/
theorem phi233_entropy_minimizer_exists
    (sigma mu : ℝ)
    (hfiber : max 0 (sigma + mu - 1) ≤ min (sigma / 2) mu) :
    ∃ a ∈ Set.Icc (max 0 (sigma + mu - 1)) (min (sigma / 2) mu),
      ∀ x ∈ Set.Icc (max 0 (sigma + mu - 1)) (min (sigma / 2) mu),
        phi233EntropyCost sigma mu a ≤ phi233EntropyCost sigma mu x := by
  exact isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hfiber)
    (continuous_phi233EntropyCost sigma mu).continuousOn

/-- The optimizer values used in Lemma 5.1(v) have a nonempty profile
fiber whenever `E < L` and `H < L`. -/
theorem phi233_selected_fiber_nonempty
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    max 0 (sigma + mu - 1) ≤ min (sigma / 2) mu := by
  dsimp
  have hL : 0 < L := lt_trans hH hHL
  have hS : 0 < 2 * H + L := by positivity
  have hT : 0 < E + L := by positivity
  have hsigma : 0 < 2 * H / (2 * H + L) := by positivity
  have hmu : 0 < E / (E + L) := by positivity
  have hhalf_sum : H / (2 * H + L) + E / (E + L) ≤ 1 := by
    have hid :
        H / (2 * H + L) + E / (E + L) =
          (H * (E + L) + E * (2 * H + L)) /
            ((2 * H + L) * (E + L)) := by
      field_simp [ne_of_gt hS, ne_of_gt hT]
    rw [hid]
    apply (div_le_one (mul_pos hS hT)).2
    have hEH : E * H < L * H := mul_lt_mul_of_pos_right hEL hH
    have hLL : 0 < L * L := mul_pos hL hL
    nlinarith
  have hsigma_le : 2 * H / (2 * H + L) ≤ 1 := by
    exact (div_le_one hS).2 (by linarith)
  apply max_le
  · exact le_min (by positivity) (le_of_lt hmu)
  · apply le_min
    · have hsigma_half :
          (2 * H / (2 * H + L)) / 2 = H / (2 * H + L) := by
        field_simp [ne_of_gt hS]
      rw [hsigma_half]
      linarith
    · linarith

end MME.StothersFourth.RemainingFour

theorem solution
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    ∃ a ∈ Set.Icc (max 0 (sigma + mu - 1)) (min (sigma / 2) mu),
      ∀ x ∈ Set.Icc (max 0 (sigma + mu - 1)) (min (sigma / 2) mu),
        (-2 * Real.negMulLog a -
            Real.negMulLog (sigma - 2 * a) -
            Real.negMulLog (mu - a) -
            Real.negMulLog (1 - sigma - mu + a)) ≤
          (-2 * Real.negMulLog x -
            Real.negMulLog (sigma - 2 * x) -
            Real.negMulLog (mu - x) -
            Real.negMulLog (1 - sigma - mu + x)) := by
  dsimp
  have hfiber :=
    MME.StothersFourth.RemainingFour.phi233_selected_fiber_nonempty
      E H L hE hH hEL hHL
  dsimp at hfiber
  obtain ⟨a, ha, hmin⟩ :=
    MME.StothersFourth.RemainingFour.phi233_entropy_minimizer_exists
      (2 * H / (2 * H + L)) (E / (E + L)) hfiber
  refine ⟨a, ha, ?_⟩
  intro x hx
  simpa only [MME.StothersFourth.RemainingFour.phi233EntropyCost] using hmin x hx
