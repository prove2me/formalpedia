-- Prove2me | Definitions.Def_Kourovka_Computability_ComputableClosure
-- name    : Kourovka_Computability_ComputableClosure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:41:57.856056+00:00
-- url     : https://prove2.me/theorems/ae0a4a75-da71-4435-ae4c-8cc0bbefae0a
-- title:
--   Computable Closure
-- statement:
--   Definitions and structural lemmas for Computable Closure, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean

import Definitions.Def_Kourovka_Computability_ComputableWords
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
def expand (conjugators xs : List G) : List G :=
  xs ++ xs.map Inv.inv ++
    xs.flatMap (fun x => xs.map (fun y => x * y)) ++
    conjugators.flatMap (fun g => xs.map (fun x => g * x * g⁻¹))
def stages (rels conjugators : List G) (n : ℕ) : List G :=
  (expand conjugators)^[n] (1 :: rels)
theorem mem_expand (C xs : List G) (x : G) :
    x ∈ expand C xs ↔ x ∈ xs ∨ (∃ y ∈ xs, y⁻¹ = x) ∨
      (∃ y ∈ xs, ∃ z ∈ xs, y * z = x) ∨
      (∃ g ∈ C, ∃ y ∈ xs, g * y * g⁻¹ = x) := by
  simp only [expand, List.mem_append, List.mem_map, List.mem_flatMap, or_assoc]
theorem subset_expand (C xs : List G) : xs ⊆ expand C xs :=
  fun x hx => (mem_expand C xs x).mpr (Or.inl hx)
theorem expand_mono {C D xs ys : List G} (hCD : C ⊆ D) (hxy : xs ⊆ ys) :
    expand C xs ⊆ expand D ys := by
  intro x hx
  rcases (mem_expand C xs x).mp hx with hx | ⟨y, hy, rfl⟩ |
    ⟨y, hy, z, hz, rfl⟩ | ⟨g, hg, y, hy, rfl⟩
  · exact (mem_expand D ys x).mpr (Or.inl (hxy hx))
  · exact (mem_expand D ys _).mpr (Or.inr (Or.inl ⟨y, hxy hy, rfl⟩))
  · exact (mem_expand D ys _).mpr (Or.inr (Or.inr (Or.inl ⟨y, hxy hy, z, hxy hz, rfl⟩)))
  · exact (mem_expand D ys _).mpr (Or.inr (Or.inr (Or.inr ⟨g, hCD hg, y, hxy hy, rfl⟩)))
@[simp] theorem stages_zero (rels C : List G) : stages rels C 0 = 1 :: rels := rfl
theorem stages_succ (rels C : List G) (n : ℕ) :
    stages rels C (n + 1) = expand C (stages rels C n) :=
  Function.iterate_succ_apply' _ _ _
theorem stages_mono_conjugators (rels : List G) {C D : List G} (hCD : C ⊆ D) (n : ℕ) :
    stages rels C n ⊆ stages rels D n := by
  induction n with
  | zero => exact List.Subset.refl _
  | succ n ih => rw [stages_succ, stages_succ]; exact expand_mono hCD ih
theorem stages_mono_depth (rels C : List G) {n m : ℕ} (hnm : n ≤ m) :
    stages rels C n ⊆ stages rels C m := by
  induction hnm with
  | refl => exact List.Subset.refl _
  | @step m hm ih =>
    rw [stages_succ]
    exact ih.trans (subset_expand _ _)
def reachable (rels : List G) : Subgroup G where
  carrier := {x | ∃ C n, x ∈ stages rels C n}
  one_mem' := ⟨[], 0, by simp⟩
  inv_mem' := by
    rintro x ⟨C, n, hx⟩
    refine ⟨C, n + 1, ?_⟩
    rw [stages_succ]
    exact (mem_expand _ _ _).mpr (Or.inr (Or.inl ⟨x, hx, rfl⟩))
  mul_mem' := by
    rintro x y ⟨C, n, hx⟩ ⟨D, m, hy⟩
    have hx' : x ∈ stages rels (C ++ D) (max n m) :=
      stages_mono_depth _ _ (le_max_left n m)
        (stages_mono_conjugators rels (by intro _ h; exact List.mem_append_left _ h) n hx)
    have hy' : y ∈ stages rels (C ++ D) (max n m) :=
      stages_mono_depth _ _ (le_max_right n m)
        (stages_mono_conjugators rels (by intro _ h; exact List.mem_append_right _ h) m hy)
    refine ⟨C ++ D, max n m + 1, ?_⟩
    rw [stages_succ]
    exact (mem_expand _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨x, hx', y, hy', rfl⟩)))
instance reachable_normal (rels : List G) : (reachable rels).Normal where
  conj_mem := by
    rintro x ⟨C, n, hx⟩ g
    have hx' : x ∈ stages rels (g :: C) n :=
      stages_mono_conjugators rels (by intro _ h; exact List.mem_cons_of_mem _ h) n hx
    refine ⟨g :: C, n + 1, ?_⟩
    rw [stages_succ]
    exact (mem_expand _ _ _).mpr (Or.inr (Or.inr (Or.inr ⟨g, by simp, x, hx', rfl⟩)))
section Computability
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
def check (input : List G × G) (certificate : List G × ℕ) : Bool :=
  decide (input.2 ∈ stages input.1 certificate.1 certificate.2)
def checkNat (input : List G × G) (certificate : ℕ) : Bool :=
  check input ((Encodable.decode (α := List G × ℕ) certificate).getD ([], 0))
end Computability
end Kourovka.MetabelianEnumeration.ComputableClosure


