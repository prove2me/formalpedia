-- Prove2me | solution 1 for emlDiag_has_minimum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:13:20.197633+00:00
-- url     : https://prove2.me/submissions/3bfd5509-2430-4af5-af90-086af8423235

-- Sol generated from Shared/AbstractAlgebra/EmlDiag.lean
import Mathlib
import Definitions.Def_Shared_AbstractAlgebra_EmlDiag

open Set

/-! # CatalogBuild.Shared.EmlDiag

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section






theorem solution:
    ∃ z₀ ∈ Ioi (0 : ℝ), ∀ z ∈ Ioi (0 : ℝ), emlDiag z₀ ≤ emlDiag z := by
  -- To find the critical points, we solve $d'(z) = 0$, which gives $z e^z = 1$.
  have h_critical : ∃ z₀ ∈ Set.Ioi 0, z₀ * Real.exp z₀ = 1 := by
    -- Apply the intermediate value theorem to the continuous function $f(z) = z e^z$ on the interval $(0, 1)$.
    have h_ivt : ∃ c ∈ Set.Ioo 0 1, c * Real.exp c = 1 := by
      apply_rules [ intermediate_value_Ioo ] <;> norm_num;
      exact continuousOn_id.mul Real.continuousOn_exp;
    exact ⟨ h_ivt.choose, h_ivt.choose_spec.1.1, h_ivt.choose_spec.2 ⟩;
  cases' h_critical with z₀ hz₀;
  refine' ⟨ z₀, hz₀.1, fun z hz => _ ⟩ ; unfold emlDiag;
  have := Real.log_le_sub_one_of_pos ( div_pos ( Real.exp_pos z ) ( Real.exp_pos z₀ ) );
  norm_num [ Real.log_div ( ne_of_gt ( Real.exp_pos z ) ) ( ne_of_gt ( Real.exp_pos z₀ ) ) ] at *;
  have := Real.log_le_sub_one_of_pos ( div_pos hz hz₀.1 );
  rw [ Real.log_div ] at this <;> nlinarith [ Real.exp_pos z, Real.exp_pos z₀, mul_div_cancel₀ ( Real.exp z ) ( ne_of_gt ( Real.exp_pos z₀ ) ), mul_div_cancel₀ ( z ) ( ne_of_gt hz₀.1 ) ]
