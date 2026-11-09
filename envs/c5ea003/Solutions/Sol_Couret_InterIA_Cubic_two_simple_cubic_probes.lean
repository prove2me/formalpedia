-- Prove2me | solution 1 for Couret.InterIA.Cubic.two_simple_cubic_probes
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:25.694124+00:00
-- url     : https://prove2.me/submissions/d9f90865-8dec-45a6-a127-b4605bed278e

import Definitions.Def_Couret_CubicReconstruction_bc5d14805c7e
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Cubic_cube_eq_probe
import Theorems.Thm_Couret_InterIA_Cubic_parameterized_rectangle_probes
import Theorems.Thm_Couret_InterIA_Cubic_probe_union
import Theorems.Thm_Couret_InterIA_Cubic_small_family_probes
import Theorems.Thm_Couret_InterIA_Cubic_square_cube_support_injective
import Definitions.Def_Couret_CubicSupport_513df21f9351
import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres



theorem realCube_injOn_fibre (n : ℕ) (hn : 0<n) (S : Finset (ZMod n)) :
    Set.InjOn realCube (cyclicFourFibre n S) := by
  intro A hA B hB he
  apply square_cube_support_injective n hn A B
  · intro z
    exact (hA.2 z).symm.trans (hB.2 z)
  · intro z
    have h := congrFun he z
    change (orderedCube A z : ℝ)=(orderedCube B z : ℝ) at h
    exact_mod_cast h

theorem p2m_local_two_simple_cubic_probes (m : ℕ) (hm : 0<m)
    (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) (hC : C.card=2)
    (hfree : AntipodalFree m C) (ha : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    ∃ Q : Finset (ZMod (2*m)), Q.card≤2 ∧
      Separates realCube (originalFibre m (C ∪ fibre (m : ZMod (2*m)) a)) Q := by
  classical
  let D0 := fibre (m : ZMod (2*m)) a
  let F := originalFibre m (C ∪ D0)
  have hi : Set.InjOn realCube F := realCube_injOn_fibre (2*m) (by omega) (C ∪ D0)
  have hD0 : D0 ∈ admissibleFullPairs m C a := admissible_full_pair_base m C a ha
  rcases admissible_full_pairs_one_or_two m hm C hC a ha with hP|⟨D,hDne,hP⟩
  · have hF : F={C ∪ D0,halfShift m C ∪ D0} := by
      dsimp [F,D0]
      rw [two_simple_fibre_rectangle m hm C a hC hfree ha,hP]
      simp [Set.pair_comm]
    apply small_family_probes realCube F hi
    right
    rw [hF]
    exact Set.ncard_pair (admissible_orientation_distinct m C a hC hfree D0 D0 hD0 hD0)
  · have hD : D ∈ admissibleFullPairs m C a := by rw [hP]; simp
    let pick (b : Bool) : {D : Finset (ZMod (2*m)) // D ∈ admissibleFullPairs m C a} :=
      if b then ⟨D,hD⟩ else ⟨D0,hD0⟩
    let g (p : Bool × Bool) := orientationCode m C a (p.1,pick p.2)
    have hg : Function.Injective g := by
      rintro ⟨p,q⟩ ⟨r,s⟩ he
      have h := orientationCode_injective m C a hC hfree he
      have h1 : p=r := congrArg Prod.fst h
      have h2 : (pick q).1=(pick s).1 := congrArg (fun t => t.2.1) h
      have hb : q=s := by
        cases q <;> cases s <;> simp_all [pick,D0]
      exact Prod.ext h1 hb
    have hmem (p : Bool × Bool) : g p ∈ F :=
      (two_simple_fibre_code_iff m hm C a hC hfree ha (g p)).mpr ⟨(p.1,pick p.2),rfl⟩
    have hcover : ∀ T ∈ F, ∃ p, g p=T := by
      intro T hT
      obtain ⟨⟨e,⟨E,hE⟩⟩,he⟩ := (two_simple_fibre_code_iff m hm C a hC hfree ha T).mp hT
      have hE' : E=D0 ∨ E=D := by simpa only [hP,Set.mem_insert_iff,Set.mem_singleton_iff] using hE
      rcases hE' with rfl|rfl
      · exact ⟨(e,false),by simpa [g,pick] using he⟩
      · exact ⟨(e,true),by simpa [g,pick] using he⟩
    let r : ZMod (2*m) → ℝ := fun z => (orderedSquare (C ∪ D0) z : ℝ)
    let H := probe r C+probe r D0
    let U := probe r (halfShift m C)-probe r C
    let V := probe r D-probe r D0
    have hCD : Disjoint C D := by obtain ⟨b,hb,hd,hs⟩ := hD; exact hd
    have hHD0 : Disjoint (halfShift m C) D0 := halfShift_disjoint_full m C a ha
    have hHD : Disjoint (halfShift m C) D :=
      orientation_disjoint_admissible m C a (halfShift m C) D (Or.inr (Set.mem_singleton _)) hD
    have hlin (p : Bool × Bool) : realCube (g p)=probe r (g p) :=
      cube_eq_probe (C ∪ D0) (g p) (hmem p).2
    have hrect : ∀ p, realCube (g p)=rectangle H U V p := by
      rintro ⟨i,j⟩
      rw [hlin]
      funext z
      cases i <;> cases j <;>
        simp only [g,pick,orientationCode,Bool.false_eq_true,↓reduceIte,
          probe_union r C D0 ha,probe_union r C D hCD,
          probe_union r (halfShift m C) D0 hHD0,probe_union r (halfShift m C) D hHD,
          rectangle,H,U,V,Pi.add_apply,Pi.sub_apply,add_zero] <;> ring
    exact parameterized_rectangle_probes realCube F g hg hmem hcover hi H U V hrect



end Couret.InterIA.Cubic

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (C :
        Finset.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
      (a :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)),
      @Eq.{1} Nat
          (@Finset.card.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            C)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        Couret.InterIA.Fibres.AntipodalFree m C →
          @Disjoint.{0}
              (Finset.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              (@Finset.partialOrder.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              (@Finset.instOrderBot.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              C
              (@Couret.InterIA.Fibres.fibre.{0}
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
                a) →
            @Exists.{1}
              (Finset.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              fun Q =>
              And
                (@LE.le.{0} Nat instLENat
                  (@Finset.card.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    Q)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Couret.InterIA.Cubic.Separates.{0, 0}
                  (Finset.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@Couret.InterIA.Cubic.realCube.{0}
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                  (Couret.InterIA.Fibres.originalFibre m
                    (@Union.union.{0}
                      (Finset.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                      (@Finset.instUnion.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                        (ZMod.decidableEq
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                      C
                      (@Couret.InterIA.Fibres.fibre.{0}
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
                        a)))
                  Q) := @_root_.Couret.InterIA.Cubic.p2m_local_two_simple_cubic_probes

