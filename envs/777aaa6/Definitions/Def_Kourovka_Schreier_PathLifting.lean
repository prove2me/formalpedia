-- Prove2me | Definitions.Def_Kourovka_Schreier_PathLifting
-- name    : Kourovka_Schreier_PathLifting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:13:54.515189+00:00
-- url     : https://prove2.me/theorems/381b2740-3d4c-4a30-9f27-e95e2ed06d62
-- title:
--   Path Lifting
-- statement:
--   Definitions and structural lemmas for Path Lifting, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Schreier/PathLifting.lean

import Definitions.Def_Kourovka_Schreier_Transversal
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_eq
import Theorems.Thm_Kourovka_Schreier_Transversal_edge_vertex
import Theorems.Thm_Kourovka_Schreier_Transversal_evaluate_of
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_eq_one
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_rep
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_right_eq
import Theorems.Thm_Kourovka_Schreier_Transversal_rep_vertex
attribute [local simp] Kourovka.Schreier.Transversal.edge_vertex
attribute [local simp] Kourovka.Schreier.Transversal.evaluate_of
attribute [local simp] Kourovka.Schreier.Transversal.rep_rep
attribute [local simp] Kourovka.Schreier.Transversal.rep_vertex


set_option autoImplicit true
namespace Kourovka.Schreier.Transversal
variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]
def walk (f : S.Edge → H) : FreeGroup X → List (X × Bool) → H
  | _, [] => 1
  | p, (x, true) :: xs => f (S.edge p x) * walk f (p * FreeGroup.of x) xs
  | p, (x, false) :: xs =>
      (f (S.edge (p * (FreeGroup.of x)⁻¹) x))⁻¹ * walk f (p * (FreeGroup.of x)⁻¹) xs
theorem mk_cons_true (x : X) (xs : List (X × Bool)) :
    FreeGroup.mk ((x, true) :: xs) = FreeGroup.of x * FreeGroup.mk xs := rfl
theorem mk_cons_false (x : X) (xs : List (X × Bool)) :
    FreeGroup.mk ((x, false) :: xs) = (FreeGroup.of x)⁻¹ * FreeGroup.mk xs := rfl
theorem walk_append (f : S.Edge → H) (p : FreeGroup X) (xs ys : List (X × Bool)) :
    S.walk f p (xs ++ ys) = S.walk f p xs * S.walk f (p * FreeGroup.mk xs) ys := by
  induction xs generalizing p with
  | nil => simp [walk, ← FreeGroup.one_eq_mk]
  | cons z xs ih => cases z with
    | mk x b => cases b <;> simp [walk, ih, mk_cons_true, mk_cons_false, mul_assoc]
theorem walk_cancel (f : S.Edge → H) (p : FreeGroup X) {xs ys : List (X × Bool)}
    (h : FreeGroup.Red.Step xs ys) : S.walk f p xs = S.walk f p ys := by
  cases h with
  | @not before after x b =>
    rw [walk_append, walk_append]
    cases b <;> simp [walk, mul_assoc]
def lift (f : S.Edge → H) (p : FreeGroup X) : FreeGroup X → H :=
  Quot.lift (S.walk f p) (fun _ _ h => S.walk_cancel f p h)
@[simp] theorem lift_mk (f : S.Edge → H) (p : FreeGroup X) (xs : List (X × Bool)) :
    S.lift f p (FreeGroup.mk xs) = S.walk f p xs := rfl
@[simp] theorem lift_one (f : S.Edge → H) (p : FreeGroup X) : S.lift f p 1 = 1 := rfl
@[simp] theorem lift_of (f : S.Edge → H) (p : FreeGroup X) (x : X) :
    S.lift f p (FreeGroup.of x) = f (S.edge p x) := by
  change f (S.edge p x) * 1 = f (S.edge p x)
  exact mul_one _
theorem lift_mul (f : S.Edge → H) (p u v : FreeGroup X) :
    S.lift f p (u * v) = S.lift f p u * S.lift f (p * u) v := by
  rcases u with ⟨xs⟩
  rcases v with ⟨ys⟩
  exact S.walk_append f p xs ys
theorem walk_start_eq (f : S.Edge → H) {p q : FreeGroup X}
    (h : S.rep p = S.rep q) (xs : List (X × Bool)) : S.walk f p xs = S.walk f q xs := by
  induction xs generalizing p q with
  | nil => rfl
  | cons z xs ih => cases z with
    | mk x b =>
      cases b
      · simp only [walk, S.edge_eq (S.rep_right_eq h (FreeGroup.of x)⁻¹) x,
          ih (S.rep_right_eq h (FreeGroup.of x)⁻¹)]
      · simp only [walk, S.edge_eq h x, ih (S.rep_right_eq h (FreeGroup.of x))]
theorem lift_start_eq (f : S.Edge → H) {p q : FreeGroup X}
    (h : S.rep p = S.rep q) (w : FreeGroup X) : S.lift f p w = S.lift f q w := by
  rcases w with ⟨xs⟩
  exact S.walk_start_eq f h xs
def subgroupLift (f : S.Edge → H) : L →* H where
  toFun u := S.lift f 1 u.val
  map_one' := rfl
  map_mul' u v := by
    change S.lift f 1 (u.val * v.val) = S.lift f 1 u.val * S.lift f 1 v.val
    rw [lift_mul]
    congr 1
    exact S.lift_start_eq f (by simpa only [one_mul, S.rep_one] using S.rep_eq_one u.property) v.val
def rewrite (p w : FreeGroup X) : FreeGroup S.Edge := S.lift FreeGroup.of p w
def rewriteWord (p : FreeGroup X) (xs : List (X × Bool)) : FreeGroup S.Edge :=
  S.walk FreeGroup.of p xs
end Kourovka.Schreier.Transversal


