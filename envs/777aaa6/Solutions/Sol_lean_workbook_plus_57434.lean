-- Prove2me | solution 1 for lean_workbook_plus_57434
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:34:33.54725+00:00
-- url     : https://prove2.me/submissions/eb53fce1-83b9-40ec-b211-478497b71445

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 1 ≠ a ∧ 1 ≠ b ∧ 1 ≠ c)
  (h₂ : a + b + c ≠ 0)
  (h₃ : a * b * c ≠ 0)
  (h₄ : a + b + c / (1 / a + 1 / b + 1 / c) ≠ 0)
  (h₅ : 1 / a + 1 / b + 1 / c ≠ 0)
  : a * b + b * c + c * a ≥ 3 * (a + b + c) / (1 / a + 1 / b + 1 / c) ↔ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a * b * c * (a + b + c) := by
  clear h₁ h₂ h₃ h₄ h₅
  rcases h₀ with ⟨ha,hb,hc⟩
  have hp : 0 < a*b*c := by positivity
  have hr : 0 < 1/a+1/b+1/c := by positivity
  have hpoly : a^2*b^2+b^2*c^2+c^2*a^2 ≥ a*b*c*(a+b+c) := by
    nlinarith only [sq_nonneg (a*b-b*c),sq_nonneg (b*c-c*a),sq_nonneg (c*a-a*b)]
  have he : (a*b+b*c+c*a)*(1/a+1/b+1/c)-3*(a+b+c) =
      (a^2*b^2+b^2*c^2+c^2*a^2-a*b*c*(a+b+c))/(a*b*c) := by
    field_simp [ne_of_gt ha,ne_of_gt hb,ne_of_gt hc]
    <;> ring
  have hn : 0 ≤ (a^2*b^2+b^2*c^2+c^2*a^2-a*b*c*(a+b+c))/(a*b*c) :=
    div_nonneg (by linarith only [hpoly]) hp.le
  have hl : a*b+b*c+c*a ≥ 3*(a+b+c)/(1/a+1/b+1/c) := by
    apply (div_le_iff₀ hr).2
    linarith only [he,hn]
  exact ⟨fun _ => hpoly,fun _ => hl⟩
