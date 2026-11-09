-- Prove2me | Definitions.Def_Couret_DisjointReduction_b47db5028f89
-- name    : Couret_DisjointReduction_b47db5028f89
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:04:41.696197+00:00
-- url     : https://prove2.me/theorems/1ea14e63-33d6-4c94-af8e-c79ae205ade7
-- title:
--   Normal forms from exchanged antipodal pairs
-- statement:
--   For finite supports $S,T$ in an abelian group, the normal-form predicate relative to $h$ is $$|S\cap T|=2,\quad S\setminus T=\{a,a+h\},\quad T\setminus S=\{b,b+h\}$$ for some $a,b$. Supporting lemmas organize four-point collisions by intersection size and half-turn exchange, enabling reduction to the two-common-point form.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/DisjointReduction.lean; source file SHA-256 f25a642b4795363a49c52f9ac0f3b54862225a8fe7459401aab2e65462b4c8da

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_StableProjection_78f7ee270976

set_option autoImplicit false
namespace Couret.InterIA.NormalForm
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def Normal (h : G) (S T : Finset G) : Prop :=
  (S ∩ T).card=2 ∧ ∃ a b, S \ T=fibre h a ∧ T \ S=fibre h b

theorem shift_twice (S : Finset G) (h : G) (hh2 : h+h=0) :
    (S.image (fun x => x+h)).image (fun x => x+h)=S := by
  rw [Finset.image_image]
  change S.image (fun x : G => (x+h)+h)=S
  have he : (fun x : G => (x+h)+h)=(fun x => x) := by
    funext x
    rw [add_assoc,hh2,add_zero]
  rw [he]
  exact Finset.image_id

theorem eq_of_full_intersection (S T : Finset G) (hS : S.card=4) (hT : T.card=4)
    (hI : (S ∩ T).card=4) : S=T := by
  have h1 : S ∩ T=S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have h2 : S ∩ T=T := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact h1.symm.trans h2

theorem disjoint_of_inter_zero (S T : Finset G) (hI : (S ∩ T).card=0) : Disjoint S T := by
  have he : S ∩ T=∅ := Finset.card_eq_zero.mp hI
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hi : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨hx,hy⟩
  rw [he] at hi
  simpa using hi

theorem doubly_disjoint_stable (S T : Finset G) (h : G) (hh2 : h+h=0)
    (hd : Disjoint S T) (hds : Disjoint S (T.image (fun x => x+h)))
    (hst : ∀ x ∈ S ∪ T, x+h ∈ S ∪ T) :
    (∀ x ∈ S, x+h ∈ S) ∧ (∀ x ∈ T, x+h ∈ T) := by
  constructor
  · intro x hx
    rcases Finset.mem_union.mp (hst x (Finset.mem_union.mpr (Or.inl hx))) with hh|hh
    · exact hh
    · have hi : x ∈ T.image (fun x => x+h) :=
        Finset.mem_image.mpr ⟨x+h,hh,by rw [add_assoc,hh2,add_zero]⟩
      exact False.elim (Finset.disjoint_left.mp hds hx hi)
  · intro x hx
    rcases Finset.mem_union.mp (hst x (Finset.mem_union.mpr (Or.inr hx))) with hh|hh
    · have hi : x+h ∈ T.image (fun x => x+h) := Finset.mem_image.mpr ⟨x,hx,rfl⟩
      exact False.elim (Finset.disjoint_left.mp hds hh hi)
    · exact hh

theorem cyclic_intersection_card_cases (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    (S ∩ T).card=0 ∨ (S ∩ T).card=2 ∨ (S ∩ T).card=4 := by
  have hu : (S ∩ T).card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
  have h1 := Couret.InterIA.Mixed.cyclic_four_intersection_ne_one m hm S T hS hT hsq
  have h3 := Couret.InterIA.IntersectionThree.cyclic_four_intersection_ne_three m hm S T hS hT hsq
  omega





end Couret.InterIA.NormalForm


