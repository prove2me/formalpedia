-- Prove2me | Definitions.Def_Kourovka_Halfspaces_HalfspaceLoopModule
-- name    : Kourovka_Halfspaces_HalfspaceLoopModule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:48:49.485633+00:00
-- url     : https://prove2.me/theorems/95c52f92-15f7-4e44-825a-fd8e978adc55
-- title:
--   Halfspace Loop Module
-- statement:
--   Definitions and structural lemmas for Halfspace Loop Module, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/HalfspaceLoopModule.lean

import Definitions.Def_Kourovka_Halfspaces_HalfspaceLoops
set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.HalfspaceLoops
open HalfspaceGeometry HalfspaceModule ValuationModule
variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)
def difference (u g : E) : Additive π.ker :=
  Additive.ofMul ⟨⁅u, g⁆, by simp [commutatorElement_def]⟩
def conjugate (g : E) (n : Additive π.ker) : Additive π.ker :=
  Additive.ofMul (MulAut.conjNormal g n.toMul)
variable [IsMulCommutative π.ker]
def height (χ : L →+ ℝ) (g : E) : ℝ := χ (π g).toAdd
def letter (g : X → E) (z : X × Bool) : E := if z.2 then g z.1 else (g z.1)⁻¹
def evalWord (g : X → E) (w : List (X × Bool)) : E :=
  FreeGroup.lift g (FreeGroup.mk w)
section CompatibleAction
variable [DecidableEq L] [Module (GroupRing L) (Additive π.ker)]
variable (hact : ∀ (p : E) (n : Additive π.ker),
  conjugate π p n = shift (-(π p).toAdd) n)
include hact
end CompatibleAction
end Kourovka.MetabelianEnumeration.HalfspaceLoops


