-- Prove2me | solution 1 for DataSheafCohomology.tri_ker_d0
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:36:42.886563+00:00
-- url     : https://prove2.me/submissions/1b10ab65-c82f-4d95-9d9b-90dc97e336a4

import Mathlib
import Definitions.Def_Algebra_DataSheafCohomology
open DataSheafCohomology in
theorem solution (K : Type*) [Field K] :
    LinearMap.ker (triD0 K) = K ∙ (fun _ => 1 : Fin 3 → K) := by
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · -- `δ⁰ f = 0` forces `f 0 = f 1 = f 2`
    intro hf
    have h0 : f 1 - f 0 = 0 := congrFun hf 0
    have h1 : f 2 - f 1 = 0 := congrFun hf 1
    refine ⟨f 0, funext fun i => ?_⟩
    fin_cases i
    · simp
    · show f 0 * 1 = f 1
      linear_combination -h0
    · show f 0 * 1 = f 2
      linear_combination -h0 - h1
  · -- constants have zero coboundary
    rintro ⟨a, rfl⟩
    funext i
    fin_cases i <;> simp [triD0]
