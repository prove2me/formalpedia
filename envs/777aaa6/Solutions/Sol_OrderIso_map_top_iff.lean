-- Prove2me | solution 1 for OrderIso.map_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:02:16.74537+00:00
-- url     : https://prove2.me/submissions/bb86a068-0f75-4423-a9eb-e223e12a04c2

import Mathlib.Order.Hom.Basic
import Definitions.Def_BruhatTits_Utils_Order

set_option autoImplicit false
variable {α β : Type*} [PartialOrder α] [PartialOrder β] (f : α ≃o β)
namespace OrderIso
theorem _root_.solution [OrderTop α] [OrderTop β] (x : α) :
    f x = ⊤ ↔ x = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ f.map_top⟩
  rw [← f.symm_apply_apply x, h, f.symm.map_top]
end OrderIso
