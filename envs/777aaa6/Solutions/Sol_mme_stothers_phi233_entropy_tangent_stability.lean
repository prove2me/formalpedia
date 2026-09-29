-- Prove2me | solution 1 for mme_stothers_phi233_entropy_tangent_stability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:38:32.060705+00:00
-- url     : https://prove2.me/submissions/50697888-935b-4f92-8c84-e5241d3ced66

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

namespace MME.StothersFourth.Phi233Tangent

private theorem negMulLog_le_tangent {r y : ℝ}
    (hr : 0 ≤ r) (hy : 0 < y) :
    Real.negMulLog r ≤
      Real.negMulLog y + (-Real.log y - 1) * (r - y) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [Real.negMulLog_zero, Real.negMulLog]
    nlinarith
  · have hratio : 0 < y / r := div_pos hy hr
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hmul := mul_le_mul_of_nonneg_left hlog hr.le
    rw [Real.log_div hy.ne' hr.ne'] at hmul
    rw [Real.negMulLog, Real.negMulLog]
    field_simp at hmul
    nlinarith

end MME.StothersFourth.Phi233Tangent

/-- A tangent certificate controls the `phi_233` maximum entropy under a
change of its two independent marginals.  The final hypothesis is exactly the
one-dimensional stationarity equation along the profile fibre. -/
theorem solution
    (a b c d a' b' c' d' sigma mu sigma' mu' : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d')
    (htotal : 2 * a + b + c + d = 1)
    (htotal' : 2 * a' + b' + c' + d' = 1)
    (hsigma : 2 * a + b = sigma) (hmu : a + c = mu)
    (hsigma' : 2 * a' + b' = sigma') (hmu' : a' + c' = mu')
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0) :
    4 * Real.negMulLog (a' / 2) +
          2 * Real.negMulLog (b' / 2) +
          2 * Real.negMulLog (c' / 2) +
          2 * Real.negMulLog (d' / 2) ≤
      4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2) +
        ((-Real.log (b / 2) - 1) - (-Real.log (d / 2) - 1)) *
          (sigma' - sigma) +
        ((-Real.log (c / 2) - 1) - (-Real.log (d / 2) - 1)) *
          (mu' - mu) := by
  let uA : ℝ := -Real.log (a / 2) - 1
  let uB : ℝ := -Real.log (b / 2) - 1
  let uC : ℝ := -Real.log (c / 2) - 1
  let uD : ℝ := -Real.log (d / 2) - 1
  have haHalf : 0 < a / 2 := div_pos ha (by norm_num)
  have hbHalf : 0 < b / 2 := div_pos hb (by norm_num)
  have hcHalf : 0 < c / 2 := div_pos hc (by norm_num)
  have hdHalf : 0 < d / 2 := div_pos hd (by norm_num)
  have ha'Half : 0 ≤ a' / 2 := div_nonneg ha' (by norm_num)
  have hb'Half : 0 ≤ b' / 2 := div_nonneg hb' (by norm_num)
  have hc'Half : 0 ≤ c' / 2 := div_nonneg hc' (by norm_num)
  have hd'Half : 0 ≤ d' / 2 := div_nonneg hd' (by norm_num)
  have hta := MME.StothersFourth.Phi233Tangent.negMulLog_le_tangent
    ha'Half haHalf
  have htb := MME.StothersFourth.Phi233Tangent.negMulLog_le_tangent
    hb'Half hbHalf
  have htc := MME.StothersFourth.Phi233Tangent.negMulLog_le_tangent
    hc'Half hcHalf
  have htd := MME.StothersFourth.Phi233Tangent.negMulLog_le_tangent
    hd'Half hdHalf
  have htangent :
      4 * Real.negMulLog (a' / 2) +
            2 * Real.negMulLog (b' / 2) +
            2 * Real.negMulLog (c' / 2) +
            2 * Real.negMulLog (d' / 2) ≤
        4 * Real.negMulLog (a / 2) +
            2 * Real.negMulLog (b / 2) +
            2 * Real.negMulLog (c / 2) +
            2 * Real.negMulLog (d / 2) +
          (2 * uA * (a' - a) + uB * (b' - b) +
            uC * (c' - c) + uD * (d' - d)) := by
    dsimp only [uA, uB, uC, uD]
    calc
      _ ≤ 4 * (Real.negMulLog (a / 2) +
              (-Real.log (a / 2) - 1) * (a' / 2 - a / 2)) +
            2 * (Real.negMulLog (b / 2) +
              (-Real.log (b / 2) - 1) * (b' / 2 - b / 2)) +
            2 * (Real.negMulLog (c / 2) +
              (-Real.log (c / 2) - 1) * (c' / 2 - c / 2)) +
            2 * (Real.negMulLog (d / 2) +
              (-Real.log (d / 2) - 1) * (d' / 2 - d / 2)) := by
          gcongr
      _ = _ := by ring
  have htotalDiff :
      2 * (a' - a) + (b' - b) + (c' - c) + (d' - d) = 0 := by
    linarith
  have hsigmaDiff : 2 * (a' - a) + (b' - b) = sigma' - sigma := by
    linarith
  have hmuDiff : (a' - a) + (c' - c) = mu' - mu := by
    linarith
  have hlinear :
      2 * uA * (a' - a) + uB * (b' - b) +
          uC * (c' - c) + uD * (d' - d) =
        (uB - uD) * (sigma' - sigma) +
          (uC - uD) * (mu' - mu) := by
    have hstation' : 2 * uA - 2 * uB - uC + uD = 0 := by
      simpa only [uA, uB, uC, uD] using hstation
    rw [← hsigmaDiff, ← hmuDiff]
    linear_combination (a' - a) * hstation' + uD * htotalDiff
  calc
    _ ≤ 4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2) +
        (2 * uA * (a' - a) + uB * (b' - b) +
          uC * (c' - c) + uD * (d' - d)) := htangent
    _ = 4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2) +
        (uB - uD) * (sigma' - sigma) +
        (uC - uD) * (mu' - mu) := by
          rw [hlinear]
          ring
    _ = _ := by ring
