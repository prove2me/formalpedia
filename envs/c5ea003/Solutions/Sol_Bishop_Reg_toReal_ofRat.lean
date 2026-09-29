-- Prove2me | solution 1 for Bishop.Reg.toReal_ofRat
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:39:15.092959+00:00
-- url     : https://prove2.me/submissions/3aa5dfcb-7a04-46a3-a474-d10ec0f7e9d8

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
open Bishop Bishop.Reg Filter Topology in
theorem solution (q : ℚ) : (ofRat q).toReal = (q : ℝ) := by
  have hap : ∀ n : ℕ, ((ofRat q).approx n) = q := fun _ => rfl
  show Filter.limUnder Filter.atTop (fun n : ℕ => (((ofRat q).approx n : ℚ) : ℝ)) = (q : ℝ)
  have h : Filter.Tendsto (fun n : ℕ => (((ofRat q).approx n : ℚ) : ℝ)) Filter.atTop
      (nhds (q : ℝ)) := by
    simp only [hap]
    exact tendsto_const_nhds
  exact h.limUnder_eq
