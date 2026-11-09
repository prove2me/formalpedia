-- Prove2me | Definitions.Def_Couret_StableFibreLift_7567a251f927
-- name    : Couret_StableFibreLift_7567a251f927
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:10:33.176928+00:00
-- url     : https://prove2.me/theorems/26fe211b-e130-4ead-9869-0760aeafc257
-- title:
--   Lifting stable four-point fibres from the half quotient
-- statement:
--   Defines the full inverse image of a finite subset modulo $m$ under projection from modulus $2m$, for $m>0$. Defines an equivalence between the square fibre of a four-element support stable under addition of $m$ and the two-element square fibre of its projected support. The inverse is full lifting, with well-definedness and inverse properties proved.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/StableFibreLift.lean; source file SHA-256 a192181d5572a38417c71aa8bfa3fcad9861ecd9e0bbfa9f3fe9c8e7aeb3b60f

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_TwoPointFibreBound_cd5b4bfd55c8

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity Couret.InterIA.Projection
open Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo

noncomputable def fullLift (m : ℕ) (hm : 0 < m) (A : Finset (ZMod m)) : Finset (ZMod (2*m)) := by
  letI : NeZero (2*m) := ⟨by omega⟩
  exact Finset.univ.filter (fun x => projection m x ∈ A)

theorem mem_fullLift (m : ℕ) (hm : 0 < m) (A : Finset (ZMod m)) (x : ZMod (2*m)) :
    x ∈ fullLift m hm A ↔ projection m x ∈ A := by
  simp [fullLift]

theorem projection_surjective (m : ℕ) : Function.Surjective (projection m) := by
  intro a
  obtain ⟨k,hk⟩ := ZMod.intCast_surjective a
  exact ⟨k,by simpa only [map_intCast] using hk⟩

theorem fullLift_stable (m : ℕ) (hm : 0 < m) (A : Finset (ZMod m)) :
    ∀ x ∈ fullLift m hm A, x+(m : ZMod (2*m)) ∈ fullLift m hm A := by
  intro x hx
  simpa only [mem_fullLift,map_add,projection_half,add_zero] using hx

theorem fullLift_image (m : ℕ) (hm : 0 < m) (A : Finset (ZMod m)) :
    (fullLift m hm A).image (projection m)=A := by
  ext a
  constructor
  · intro ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact (mem_fullLift m hm A x).mp hx
  · intro ha
    obtain ⟨x,rfl⟩ := projection_surjective m a
    exact Finset.mem_image.mpr ⟨x,(mem_fullLift m hm A x).mpr ha,rfl⟩

theorem fullLift_of_stable (m : ℕ) (hm : 0 < m) (S : Finset (ZMod (2*m)))
    (hs : ∀ x ∈ S, x+m ∈ S) : fullLift m hm (S.image (projection m))=S := by
  ext x
  exact (mem_fullLift m hm _ x).trans (stable_saturated m hm S hs x)

theorem fullLift_pair (m : ℕ) (hm : 0 < m) (a b : ZMod (2*m)) :
    fullLift m hm {projection m a,projection m b}=
      fibre (m : ZMod (2*m)) a ∪ fibre (m : ZMod (2*m)) b := by
  ext x
  simp only [mem_fullLift,Finset.mem_insert,Finset.mem_singleton,Finset.mem_union,fibre]
  have ha : projection m x=projection m a ↔ x=a ∨ x=a+m :=
    eq_comm.trans (projection_eq_iff m hm a x)
  have hb : projection m x=projection m b ↔ x=b ∨ x=b+m :=
    eq_comm.trans (projection_eq_iff m hm b x)
  rw [ha,hb]

theorem fullLift_card_four (m : ℕ) (hm : 0 < m) (A : Finset (ZMod m)) (hA : A.card=2) :
    (fullLift m hm A).card=4 := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hA
  obtain ⟨x,rfl⟩ := projection_surjective m a
  obtain ⟨y,rfl⟩ := projection_surjective m b
  have hd : Disjoint (fibre (m : ZMod (2*m)) x) (fibre (m : ZMod (2*m)) y) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have h1 : projection m z=projection m x := by
      rcases Finset.mem_insert.mp hz with rfl|hz
      · rfl
      · rw [Finset.mem_singleton.mp hz,map_add,projection_half,add_zero]
    have h2 : projection m z=projection m y := by
      rcases Finset.mem_insert.mp hz' with rfl|hz'
      · rfl
      · rw [Finset.mem_singleton.mp hz',map_add,projection_half,add_zero]
    exact hab (h1.symm.trans h2)
  rw [fullLift_pair,Finset.card_union_of_disjoint hd,
    fibre_card _ x (Couret.InterIA.L4.half_ne_zero m hm),
    fibre_card _ y (Couret.InterIA.L4.half_ne_zero m hm)]

theorem stable_collision_stable (m : ℕ) (hm : 0 < m) (S T : Finset (ZMod (2*m)))
    (hs : ∀ x ∈ S, x+m ∈ S) (heq : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∀ x ∈ T, x+m ∈ T := by
  intro x hx
  have hS : x ∈ S ↔ x+(m : ZMod (2*m)) ∈ S := by
    constructor
    · exact hs x
    · intro h
      simpa only [add_assoc,Couret.InterIA.L4.half_add_half,add_zero] using hs (x+m) h
  have hd := even_symmetric_difference_stable m hm S T heq x
  simp only [Finset.mem_symmDiff] at hd
  tauto

/-- The two possible representatives of each quotient equation contribute exactly once. -/
theorem quotient_equation_count (m : ℕ) (hm : 0 < m) (x z : ZMod (2*m)) :
    (if x=z then 1 else 0 : ℕ)+(if x=z-m then 1 else 0)=
      if projection m x=projection m z then 1 else 0 := by
  have hh := Couret.InterIA.L4.half_ne_zero m hm
  have he : x=z-m ↔ z=x+(m : ZMod (2*m)) := by constructor <;> intro h <;> rw [h] <;> abel
  simp only [projection_eq_iff m hm,← he]
  by_cases h1 : x=z
  · have h2 : x ≠ z-m := by
      intro h2
      have hz : z=z+(m : ZMod (2*m)) := by simpa only [h1] using he.mp h2
      exact hh (add_left_cancel (by simpa using hz.symm : z+m=z+0))
    simp only [if_pos h1,if_neg h2,if_pos (Or.inl h1.symm),add_zero]
  · simp [h1,eq_comm]

theorem quotient_pair_profile (m : ℕ) (hm : 0 < m) (a b z : ZMod (2*m)) :
    Couret.InterIA.TwoPoint.pairCoeff a b z+Couret.InterIA.TwoPoint.pairCoeff a b (z-m)=
      Couret.InterIA.TwoPoint.pairCoeff (projection m a) (projection m b) (projection m z) := by
  have h1 := quotient_equation_count m hm (a+a) z
  have h2 := quotient_equation_count m hm (b+b) z
  have h3 := quotient_equation_count m hm (a+b) z
  simp only [map_add] at h1 h2 h3
  unfold Couret.InterIA.TwoPoint.pairCoeff
  omega

theorem stable_four_square_formula (m : ℕ) (hm : 0 < m)
    (S : Finset (ZMod (2*m))) (hS : S.card=4) (hs : ∀ x ∈ S, x+m ∈ S)
    (z : ZMod (2*m)) :
    orderedSquare S z=2*orderedSquare (S.image (projection m)) (projection m z) := by
  obtain ⟨a,b,hab,hd,hSe⟩ := stable_four_split S m (Couret.InterIA.L4.half_ne_zero m hm)
    (Couret.InterIA.L4.half_add_half m) hS hs
  have hab' : a ≠ b := by intro he; subst b; exact hab rfl
  have hi : indicator S=(1+atom (m : ZMod (2*m)))*indicator {a,b} := by
    rw [hSe,indicator_union_disjoint _ _ hd,indicator_fibre _ _ (Couret.InterIA.L4.half_ne_zero m hm),
      indicator_fibre _ _ (Couret.InterIA.L4.half_ne_zero m hm),indicator_pair a b hab',mul_add]
  have hH : atom (m : ZMod (2*m))*atom (m : ZMod (2*m))=1 := by
    exact antipodal_monomial_square (m : ZMod (2*m)) (Couret.InterIA.L4.half_add_half m)
  have hsq : indicator S*indicator S=
      2*(indicator {a,b}*indicator {a,b}+atom (m : ZMod (2*m))*(indicator {a,b}*indicator {a,b})) := by
    rw [hi]
    calc _ = ((1+atom (m : ZMod (2*m)))*(1+atom (m : ZMod (2*m))))*(indicator {a,b}*indicator {a,b}) := by ring
         _ = _ := by rw [Couret.InterIA.L4.antipodal_square _ hH]; ring
  have hc := congrArg (fun f : AddMonoidAlgebra ℤ (ZMod (2*m)) => f.coeff z) hsq
  change (indicator S*indicator S).coeff z = _ at hc
  simp only [two_mul,AddMonoidAlgebra.coeff_add] at hc
  change _ = (indicator {a,b}*indicator {a,b}).coeff z+
    (atom (m : ZMod (2*m))*(indicator {a,b}*indicator {a,b})).coeff z+
    ((indicator {a,b}*indicator {a,b}).coeff z+
    (atom (m : ZMod (2*m))*(indicator {a,b}*indicator {a,b})).coeff z) at hc
  unfold atom at hc
  rw [monomial_translate_coefficient,indicator_square_coefficient,
    indicator_square_coefficient,indicator_square_coefficient] at hc
  have hn : orderedSquare S z=2*(orderedSquare {a,b} z+orderedSquare {a,b} (z-m)) := by omega
  rw [hn,Couret.InterIA.TwoPoint.actual_pair_coefficient a b z hab',
    Couret.InterIA.TwoPoint.actual_pair_coefficient a b (z-m) hab',quotient_pair_profile m hm]
  rw [hSe,Finset.image_union,projection_fibre_image,projection_fibre_image]
  simp only [Finset.singleton_union]
  rw [Couret.InterIA.TwoPoint.actual_pair_coefficient _ _ _ (projection_distinct m hm a b hab)]

theorem stable_four_square_iff_quotient (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hs : ∀ x ∈ S, x+m ∈ S) (ht : ∀ x ∈ T, x+m ∈ T) :
    (∀ z, orderedSquare S z=orderedSquare T z) ↔
      ∀ z, orderedSquare (S.image (projection m)) z=orderedSquare (T.image (projection m)) z := by
  constructor
  · exact stable_four_quotient_collision m hm S T hS hT hs ht
  · intro he z
    rw [stable_four_square_formula m hm S hS hs,stable_four_square_formula m hm T hT ht,he]

noncomputable def stableFourFibreEquiv (m : ℕ) (hm : 0 < m)
    (S : Finset (ZMod (2*m))) (hS : S.card=4) (hs : ∀ x ∈ S, x+m ∈ S) :
    originalFibre m S ≃ pairFibre m (S.image (projection m)) where
  toFun T := ⟨T.val.image (projection m),
    stable_four_image_card m hm T.val T.property.1 (stable_collision_stable m hm S T.val hs T.property.2),
    stable_four_quotient_collision m hm S T.val hS T.property.1 hs
      (stable_collision_stable m hm S T.val hs T.property.2) T.property.2⟩
  invFun A := ⟨fullLift m hm A.val,fullLift_card_four m hm A.val A.property.1,
    (stable_four_square_iff_quotient m hm S (fullLift m hm A.val) hS
      (fullLift_card_four m hm A.val A.property.1) hs (fullLift_stable m hm A.val)).mpr
      (by rw [fullLift_image]; exact A.property.2)⟩
  left_inv T := Subtype.ext (fullLift_of_stable m hm T.val
    (stable_collision_stable m hm S T.val hs T.property.2))
  right_inv A := Subtype.ext (fullLift_image m hm A.val)

theorem stable_four_fibre_ncard (m : ℕ) (hm : 0 < m)
    (S : Finset (ZMod (2*m))) (hS : S.card=4) (hs : ∀ x ∈ S, x+m ∈ S) :
    (originalFibre m S).ncard=1 ∨ (originalFibre m S).ncard=2 := by
  have he : (originalFibre m S).ncard=(pairFibre m (S.image (projection m))).ncard :=
    Nat.card_congr (stableFourFibreEquiv m hm S hS hs)
  rw [he]
  exact cyclic_pair_fibre_ncard m hm _ (stable_four_image_card m hm S hS hs)

end Couret.InterIA.Fibres


