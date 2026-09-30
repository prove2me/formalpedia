-- Prove2me | solution 1 for lean_workbook_plus_55105
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:08:56.822612+00:00
-- url     : https://prove2.me/submissions/b6f236b5-4a9d-46dd-b6f9-f336bf347b99

import Mathlib
set_option autoImplicit false

theorem solution (E : Type) : ¬∃ f : E → Set E, Function.Surjective f   := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha⟩ := hf {e : E | e ∉ f e}
  have hdiag : a ∈ f a ↔ a ∉ f a :=
    Iff.of_eq (congrArg (fun s : Set E => a ∈ s) ha)
  have hnot : a ∉ f a := fun hm => (hdiag.mp hm) hm
  exact hnot (hdiag.mpr hnot)

#print axioms solution
