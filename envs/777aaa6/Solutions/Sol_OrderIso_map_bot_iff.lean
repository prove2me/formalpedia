-- Prove2me | solution 1 for OrderIso.map_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:02:19.605027+00:00
-- url     : https://prove2.me/submissions/6dc166fd-efc0-4456-b31e-44ec6dca6f11

import Mathlib.Order.Hom.Basic
import Definitions.Def_BruhatTits_Utils_Order

set_option autoImplicit false
variable {α β : Type*} [PartialOrder α] [PartialOrder β] (f : α ≃o β)
namespace OrderIso
theorem _root_.solution [OrderBot α] [OrderBot β] (x : α) :
    f x = ⊥ ↔ x = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ f.map_bot⟩
  rw [← f.symm_apply_apply x, h, f.symm.map_bot]
end OrderIso
