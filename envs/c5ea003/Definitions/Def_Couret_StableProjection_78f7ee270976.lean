-- Prove2me | Definitions.Def_Couret_StableProjection_78f7ee270976
-- name    : Couret_StableProjection_78f7ee270976
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:03:35.568189+00:00
-- url     : https://prove2.me/theorems/67506d8b-7f06-4bcc-9a7a-112064d9151b
-- title:
--   Projection through the half-period quotient
-- statement:
--   For a cyclic group $\mathbb Z/(2m)$, the quotient projection maps to $\mathbb Z/m$ and induces a group-ring pushforward. Supporting lemmas describe half-turn-stable four-point supports as unions of two antipodal pairs and track their image under projection. This converts stable-support collision questions into a smaller cyclic quotient.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/StableProjection.lean; source file SHA-256 6ce8aa246312a4979a5fa5cefe9a796e2df61ddcdc38e08f0109e9e007cd5feb

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
import Definitions.Def_Couret_MixedGeometry_fb699ea460d2
import Definitions.Def_Couret_IntersectionTwo_2d7b2419466c
import Mathlib.Algebra.MonoidAlgebra.MapDomain

set_option autoImplicit false
namespace Couret.InterIA.Projection
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.GroupRing

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem stable_four_split (S : Finset G) (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (hS : S.card=4) (hst : ∀ x ∈ S, x+h ∈ S) :
    ∃ a b, fibre h a ≠ fibre h b ∧ Disjoint (fibre h a) (fibre h b) ∧
      S=fibre h a ∪ fibre h b := by
  have hc := twice_fibres_card h hh hh2 S hst
  have hc2 : (fibres h S).card=2 := by omega
  obtain ⟨A,B,hAB,hfamily⟩ := Finset.card_eq_two.mp hc2
  have hA : A ∈ fibres h S := by rw [hfamily]; simp
  have hB : B ∈ fibres h S := by rw [hfamily]; simp
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
  refine ⟨a,b,hAB,?_,?_⟩
  · exact fibres_pairwise_disjoint h hh2 S
      (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩) hAB
  · have he := fibres_union h S hst
    rw [hfamily] at he
    simpa using he.symm

def projection (m : ℕ) : ZMod (2*m) →+* ZMod m :=
  ZMod.castHom (dvd_mul_left m 2) (ZMod m)

theorem projection_half (m : ℕ) : projection m (m : ZMod (2*m))=0 := by
  simp [projection]

theorem projection_kernel (m : ℕ) (hm : 0 < m) (x : ZMod (2*m)) :
    projection m x=0 ↔ x=0 ∨ x=m := by
  letI : NeZero (2*m) := ⟨by omega⟩
  constructor
  · intro hx
    have hv : (x.val : ZMod m)=0 := by
      have he := congrArg (projection m) (ZMod.natCast_zmod_val x)
      simpa only [map_natCast,hx] using he
    obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff x.val m).mp hv
    have he : x=(m : ZMod (2*m))*(k : ZMod (2*m)) := by
      rw [← ZMod.natCast_zmod_val x,hk,Nat.cast_mul]
    have hd : x+x=0 := by
      calc x+x=((m : ZMod (2*m))+m)*k := by rw [he]; ring
           _=0 := by rw [Couret.InterIA.L4.half_add_half,zero_mul]
    exact Couret.InterIA.L4.doubling_kernel m hm x hd
  · rintro (rfl|rfl)
    · exact map_zero _
    · exact projection_half m

theorem projection_eq_iff (m : ℕ) (hm : 0 < m) (x y : ZMod (2*m)) :
    projection m x=projection m y ↔ y=x ∨ y=x+m := by
  rw [← sub_eq_zero,← map_sub,projection_kernel m hm]
  constructor
  · rintro (hz|hz)
    · exact Or.inl (sub_eq_zero.mp hz).symm
    · right
      have hh2 := Couret.InterIA.L4.half_add_half m
      have he : x=y+m := by
        calc x=(x-y)+y := by abel
             _=y+m := by rw [hz]; abel
      calc y=y+(m+m) := by rw [hh2,add_zero]
           _=(y+m)+m := by abel
           _=x+m := by rw [he]
  · rintro (rfl|rfl)
    · exact Or.inl (sub_self _)
    · right
      calc x-(x+m) = - (m : ZMod (2*m)) := by abel
           _ = m := by
             have hh := Couret.InterIA.L4.half_add_half m
             exact neg_eq_of_add_eq_zero_left hh

theorem projection_fibre_image (m : ℕ) (a : ZMod (2*m)) :
    (fibre (m : ZMod (2*m)) a).image (projection m)={projection m a} := by
  simp [fibre,map_add,projection_half]

theorem projection_distinct (m : ℕ) (hm : 0 < m) (a b : ZMod (2*m))
    (hne : fibre (m : ZMod (2*m)) a ≠ fibre (m : ZMod (2*m)) b) :
    projection m a ≠ projection m b := by
  intro he
  rcases (projection_eq_iff m hm a b).mp he with rfl|rfl
  · exact hne rfl
  · exact hne (fibre_partner (m : ZMod (2*m)) a (Couret.InterIA.L4.half_add_half m)).symm

theorem stable_four_image_card (m : ℕ) (hm : 0 < m) (S : Finset (ZMod (2*m)))
    (hS : S.card=4) (hst : ∀ x ∈ S, x+m ∈ S) : (S.image (projection m)).card=2 := by
  obtain ⟨a,b,hab,hd,hSe⟩ := stable_four_split S m (Couret.InterIA.L4.half_ne_zero m hm)
    (Couret.InterIA.L4.half_add_half m) hS hst
  rw [hSe,Finset.image_union,projection_fibre_image,projection_fibre_image]
  simpa using Finset.card_pair (projection_distinct m hm a b hab)

noncomputable def push (m : ℕ) : AddMonoidAlgebra ℤ (ZMod (2*m)) →+*
    AddMonoidAlgebra ℤ (ZMod m) :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (projection m).toAddMonoidHom

theorem push_single (m : ℕ) (a : ZMod (2*m)) (n : ℤ) :
    push m (AddMonoidAlgebra.single a n)=AddMonoidAlgebra.single (projection m a) n := by
  exact AddMonoidAlgebra.mapDomain_single

theorem push_fibre (m : ℕ) (hm : 0 < m) (a : ZMod (2*m)) :
    push m (indicator (fibre (m : ZMod (2*m)) a))=
      2*(AddMonoidAlgebra.single (projection m a) (1 : ℤ)) := by
  have hn : a ≠ a+m := by
    intro he
    exact Couret.InterIA.L4.half_ne_zero m hm (add_left_cancel (by simpa using he.symm : a+m=a+0))
  rw [fibre,Couret.InterIA.IntersectionTwo.indicator_pair a (a+m) hn,map_add]
  change push m (AddMonoidAlgebra.single a 1)+push m (AddMonoidAlgebra.single (a+m) 1)=_
  rw [push_single,push_single,map_add,projection_half,add_zero]
  ring

/-- The factor two is on the projected indicator, not asserted by an enumeration. -/
theorem push_stable_four_indicator (m : ℕ) (hm : 0 < m) (S : Finset (ZMod (2*m)))
    (hS : S.card=4) (hst : ∀ x ∈ S, x+m ∈ S) :
    push m (indicator S)=2*indicator (S.image (projection m)) := by
  obtain ⟨a,b,hab,hd,hSe⟩ := stable_four_split S m (Couret.InterIA.L4.half_ne_zero m hm)
    (Couret.InterIA.L4.half_add_half m) hS hst
  rw [hSe,Couret.InterIA.IntersectionTwo.indicator_union_disjoint _ _ hd,map_add,
    push_fibre m hm a,push_fibre m hm b,Finset.image_union,
    projection_fibre_image,projection_fibre_image]
  simp only [Finset.singleton_union]
  rw [Couret.InterIA.IntersectionTwo.indicator_pair _ _ (projection_distinct m hm a b hab)]
  change 2*AddMonoidAlgebra.single (projection m a) 1+
    2*AddMonoidAlgebra.single (projection m b) 1 =
    2*(AddMonoidAlgebra.single (projection m a) 1+AddMonoidAlgebra.single (projection m b) 1)
  ring

theorem stable_four_quotient_collision (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hSs : ∀ x ∈ S, x+m ∈ S) (hTs : ∀ x ∈ T, x+m ∈ T)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∀ z, orderedSquare (S.image (projection m)) z=orderedSquare (T.image (projection m)) z := by
  have he := congrArg (push m) ((square_equality_iff S T).mpr hsq)
  rw [map_mul,map_mul,push_stable_four_indicator m hm S hS hSs,
    push_stable_four_indicator m hm T hT hTs] at he
  apply (square_equality_iff _ _).mp
  have hz : (2 : AddMonoidAlgebra ℤ (ZMod m)) *
      (2*(indicator (S.image (projection m))*indicator (S.image (projection m)) -
        indicator (T.image (projection m))*indicator (T.image (projection m))))=0 := by
    calc _ = (2*indicator (S.image (projection m)))*(2*indicator (S.image (projection m))) -
      (2*indicator (T.image (projection m)))*(2*indicator (T.image (projection m))) := by ring
         _ = 0 := by rw [he]; simp
  exact sub_eq_zero.mp (integer_coefficient_no_two_torsion _
    (integer_coefficient_no_two_torsion _ hz))

theorem stable_saturated (m : ℕ) (hm : 0 < m) (S : Finset (ZMod (2*m)))
    (hst : ∀ x ∈ S, x+m ∈ S) (x : ZMod (2*m)) :
    projection m x ∈ S.image (projection m) ↔ x ∈ S := by
  constructor
  · intro hx
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hx
    rcases (projection_eq_iff m hm a x).mp he with rfl|rfl
    · exact ha
    · exact hst a ha
  · exact fun hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩





end Couret.InterIA.Projection


