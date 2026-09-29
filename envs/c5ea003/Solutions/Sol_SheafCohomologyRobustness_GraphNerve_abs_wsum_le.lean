-- Prove2me | solution 1 for SheafCohomologyRobustness.GraphNerve.abs_wsum_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:13:46.777189+00:00
-- url     : https://prove2.me/submissions/4521be4a-a263-47ae-9b4c-f1dd472f3c37

import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
open SheafCohomologyRobustness GraphNerve in
theorem solution {ι : Type*} {A : ι → ι → Prop} {c : ι → ι → ℝ} {ε : ℝ}
    (hb : ∀ x y, A x y → |c x y| ≤ ε) :
    ∀ (i : ι) (l : List ι), IsWalk A i l → |wsum c i l| ≤ l.length * ε := by
  intro i l
  induction l generalizing i with
  | nil => intro _; simp [wsum]
  | cons j t ih =>
    rintro ⟨hij, ht⟩
    -- triangle inequality, one step at a time
    have h1 := hb i j hij
    have h2 := ih j ht
    show |c i j + wsum c j t| ≤ ((t.length + 1 : ℕ) : ℝ) * ε
    calc |c i j + wsum c j t| ≤ |c i j| + |wsum c j t| := abs_add_le _ _
      _ ≤ ε + t.length * ε := add_le_add h1 h2
      _ = ((t.length + 1 : ℕ) : ℝ) * ε := by push_cast; ring
