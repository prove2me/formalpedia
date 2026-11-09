-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Orbits.normal_form_orbit_shapes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:43.961201+00:00
-- url     : https://prove2.me/submissions/ba3a6f6a-7065-47c1-906e-39813d5620b2

import Definitions.Def_Couret_OrbitAssembly_415e94ef1ad8
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Orbits_normal_form_geometric_data
import Theorems.Thm_Couret_InterIA_Catalogue_residual_four_atoms
import Definitions.Def_Couret_OrbitGeometry_a2664a5897aa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Orbits
open Finset Couret.InterIA.Catalogue Couret.InterIA.Projection Couret.InterIA.Fibres
open Couret.InterIA.Parity

theorem projection_common_separated (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (a c : ZMod (2*m))
    (ha : Disjoint C (fibre (m : ZMod (2*m)) a)) (hc : c ∈ C) :
    projection m c ≠ projection m a := by
  intro he
  have hf : c ∈ fibre (m : ZMod (2*m)) a := by
    rcases (projection_eq_iff m hm a c).mp he.symm with h|h
    · simp [fibre,h]
    · simp [fibre,h]
  exact Finset.disjoint_left.mp ha hc hf





theorem p2m_local_normal_form_orbit_shapes (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m)))
    (hn : Couret.InterIA.NormalForm.Normal (m : ZMod (2*m)) S T)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) : OrbitShape m S T := by
  obtain ⟨a,b,hU,hV,ha,hb,hd,he,ho⟩ := normal_form_geometric_data m hm S T hn hsq
  obtain ⟨c,d,hcd,hCe,hfour⟩ := residual_four_atoms m (S ∩ T) hn.1 a b
  have hcm : c ∈ S ∩ T := by rw [hCe]; simp
  have hdm : d ∈ S ∩ T := by rw [hCe]; simp
  have hca := projection_common_separated m hm (S ∩ T) a c ha hcm
  have hcb := projection_common_separated m hm (S ∩ T) b c hb hcm
  have hda := projection_common_separated m hm (S ∩ T) a d ha hdm
  have hdb := projection_common_separated m hm (S ∩ T) b d hb hdm
  have hw : residual m (S ∩ T) a b=
      atoms (projection m a) (projection m b) (projection m c) (projection m d) := by
    rw [hfour]
    dsimp [atoms,A]
    abel
  rw [hw] at he
  have hcl := atoms_translation_closed (projection m a) (projection m b)
    (projection m c) (projection m d) (projection m (b-a)) he
  have hba : projection m b=projection m a+projection m (b-a) := by rw [map_sub]; abel
  refine ⟨a,b,c,d,hU,hV,hcd,hCe,hca,hcb,hda,hdb,?_⟩
  rcases ho with h2|h4
  · have hz : projection m (b-a)+projection m (b-a)=0 := by
      have hz := addOrderOf_nsmul_eq_zero (projection m (b-a))
      simpa only [h2,two_nsmul] using hz
    exact Or.inl ⟨h2,period_two_shape _ _ _ _ _ hd hz hba hca hcb hcl⟩
  · exact Or.inr ⟨h4,period_four_shape _ _ _ _ _ h4 hba hcl⟩



end Couret.InterIA.Catalogue.Orbits

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (S T :
        Finset.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
      @Couret.InterIA.NormalForm.Normal.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
          (@Ring.toAddCommGroup.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            (@CommRing.toRing.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (ZMod.commRing
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
          (ZMod.decidableEq
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
          (@Nat.cast.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            (@AddMonoidWithOne.toNatCast.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@Ring.toAddGroupWithOne.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@CommRing.toRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
            m)
          S T →
        (∀
            (z :
              ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)),
            @Eq.{1} Nat
              (@Couret.InterIA.Parity.orderedSquare.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@Ring.toAddCommGroup.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@CommRing.toRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
                (ZMod.decidableEq
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                S z)
              (@Couret.InterIA.Parity.orderedSquare.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                (@Ring.toAddCommGroup.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@CommRing.toRing.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (ZMod.commRing
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
                (ZMod.decidableEq
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                T z)) →
          Couret.InterIA.Catalogue.Orbits.OrbitShape m S T := @_root_.Couret.InterIA.Catalogue.Orbits.p2m_local_normal_form_orbit_shapes

