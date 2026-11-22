-- Prove2me | Definitions.Def_Kourovka_Halfspaces_SchreierHeights
-- name    : Kourovka_Halfspaces_SchreierHeights
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:15:50.579289+00:00
-- url     : https://prove2.me/theorems/fd8e13e3-6f49-47de-8fd8-ef95723bd5c6
-- title:
--   Schreier Heights
-- statement:
--   Definitions and structural lemmas for Schreier Heights, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Halfspaces/SchreierHeights.lean

import Definitions.Def_Kourovka_Halfspaces_HalfspaceGeometry
import Definitions.Def_Kourovka_Schreier_PathLifting
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_rewrite_mk
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.rewrite_mk


set_option autoImplicit true
noncomputable section
namespace Kourovka.MetabelianEnumeration.SchreierHeights
open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal
variable {X Q : Type*} [CommGroup Q]
def value (θ : FreeGroup X →* Multiplicative ℝ) (w : FreeGroup X) : ℝ := (θ w).toAdd
@[simp] theorem value_one (θ : FreeGroup X →* Multiplicative ℝ) : value θ 1 = 0 := by
  simp [value]
@[simp] theorem value_mul (θ : FreeGroup X →* Multiplicative ℝ) (u v : FreeGroup X) :
    value θ (u * v) = value θ u + value θ v := by simp [value]
@[simp] theorem value_inv (θ : FreeGroup X →* Multiplicative ℝ) (u : FreeGroup X) :
    value θ u⁻¹ = -value θ u := by simp [value]
def representativeOfSection (π : FreeGroup X →* Q) (r : Q → FreeGroup X)
    (hr : ∀ q, π (r q) = q) (h1 : r 1 = 1) : Transversal π.ker where
  rep w := r (π w)
  sameCoset w := by simp [MonoidHom.mem_ker, hr]
  constantOnCosets := by
    intro g h hgh
    have heq : π g = π h := by
      apply mul_inv_eq_one.mp
      simpa [MonoidHom.mem_ker] using hgh
    rw [heq]
  rep_one := by rw [map_one, h1]
def symbolsIn (θ : FreeGroup X →* Multiplicative ℝ)
    {L : Subgroup (FreeGroup X)} (S : Transversal L) (P : ℝ → Prop) :
    Set (S.Edge) :=
  {z | P (value θ z.1.val) ∧ P (value θ (z.1.val * FreeGroup.of z.2))}
end Kourovka.MetabelianEnumeration.SchreierHeights


