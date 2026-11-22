-- Prove2me | Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting
-- name    : Kourovka_Halfspaces_HalfspaceSplitting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:46:12.363701+00:00
-- url     : https://prove2.me/theorems/c5ad9b47-0ea2-4e9b-beaa-68c80e839553
-- title:
--   Halfspace Splitting
-- statement:
--   Definitions and structural lemmas for Halfspace Splitting, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceSplitting.lean

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Mathlib.GroupTheory.HNNExtension
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.HalfspaceSplitting
variable {N : Type*} [Group N]
abbrev Twist (C : Subgroup N) := HNNExtension N C C (MulEquiv.refl C)
def left (C : Subgroup N) : N →* Twist C := HNNExtension.of
def right (C : Subgroup N) : N →* Twist C :=
  ((MulAut.conj (HNNExtension.t⁻¹ : Twist C)).toMonoidHom).comp HNNExtension.of
end Kourovka.MetabelianEnumeration.HalfspaceSplitting


