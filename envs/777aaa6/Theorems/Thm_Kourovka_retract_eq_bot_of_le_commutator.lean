-- Prove2me | Theorems.Thm_Kourovka_retract_eq_bot_of_le_commutator
-- name    : Kourovka.retract_eq_bot_of_le_commutator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:38:05.809742+00:00
-- url     : https://prove2.me/theorems/383b6012-9192-4346-b7dd-5771e43722df
-- title:
--   Kourovka: retract eq bot of le commutator
-- statement:
--   A soluble retract contained in the derived subgroup is trivial.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralProducts.lean#L122-L133
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralProducts.lean#L122-L133

import Definitions.Def_Kourovka_Components
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_Kourovka_CentralProducts
set_option autoImplicit true
open Kourovka
variable {G : Type*} [Group G]

theorem Kourovka.retract_eq_bot_of_le_commutator [IsSolvable G] (T : Subgroup G)
    (r : G →* T) (hr : ∀ t : T, r t = t) (hT : T ≤ commutator G) : T = ⊥ := by sorry
