-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.matching_rows_zero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:44.725711+00:00
-- url     : https://prove2.me/submissions/8331bbe9-7cfd-4275-ada9-38021811a8e8

import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_permutation_indices
import Theorems.Thm_Couret_InterIA_SingletonNecessity_zip_mapped_eq
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



theorem p2m_local_matching_rows_zero (x : Fin 6 → G) (L R : List Vec)
    (hp : (L.map (evaluation x)).Perm (R.map (evaluation x))) :
    ∃ p : List ℕ, p.Perm (List.range R.length) ∧
      ∀ v ∈ ((L.zip p).map fun (v,j) => v-R[j]!), evaluation x v=0 := by
  letI : Inhabited G := ⟨0⟩
  obtain ⟨p,hp,he⟩ := permutation_indices (L.map (evaluation x)) (R.map (evaluation x)) hp
  have hpr : p.Perm (List.range R.length) := by simpa only [List.length_map] using hp
  refine ⟨p,hpr,?_⟩
  intro v hv
  obtain ⟨⟨w,j⟩,hm,rfl⟩ := List.mem_map.mp hv
  have hj : j<R.length := List.mem_range.mp (hpr.mem_iff.mp (List.of_mem_zip hm).2)
  have h := zip_mapped_eq L p (evaluation x) (fun j => (R.map (evaluation x))[j]!) he w j hm
  have hg : (R.map (evaluation x))[j]! = evaluation x R[j]! := by
    rw [getElem!_pos (R.map (evaluation x)) j (by simpa using hj),
      getElem!_pos R j hj,List.getElem_map]
  change evaluation x w=(R.map (evaluation x))[j]! at h
  rw [hg] at h
  simpa only [map_sub,sub_eq_zero] using h





end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G)
  (L R : List.{0} Couret.InterIA.SingletonNecessity.Vec),
  @List.Perm.{p2m_u_0} G
      (@List.map.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
        (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
          (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
            (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
              (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
            (@AddZeroClass.toAddZero.{p2m_u_0} G
              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
          Couret.InterIA.SingletonNecessity.Vec (fun x => G)
          (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
            (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
              (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
            (@AddZeroClass.toAddZero.{p2m_u_0} G
              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
          (@Couret.InterIA.SingletonNecessity.evaluation.{p2m_u_0} G inst x))
        L)
      (@List.map.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
        (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
          (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
            (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
              (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
            (@AddZeroClass.toAddZero.{p2m_u_0} G
              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
          Couret.InterIA.SingletonNecessity.Vec (fun x => G)
          (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
            (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
              (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
            (@AddZeroClass.toAddZero.{p2m_u_0} G
              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
          (@Couret.InterIA.SingletonNecessity.evaluation.{p2m_u_0} G inst x))
        R) →
    @Exists.{1} (List.{0} Nat) fun p =>
      And (@List.Perm.{0} Nat p (List.range (@List.length.{0} Couret.InterIA.SingletonNecessity.Vec R)))
        (∀ (v : Couret.InterIA.SingletonNecessity.Vec),
          @Membership.mem.{0, 0} Couret.InterIA.SingletonNecessity.Vec (List.{0} Couret.InterIA.SingletonNecessity.Vec)
              (@List.instMembership.{0} Couret.InterIA.SingletonNecessity.Vec)
              (@List.map.{0, 0} (Prod.{0, 0} Couret.InterIA.SingletonNecessity.Vec Nat)
                Couret.InterIA.SingletonNecessity.Vec
                (fun x =>
                  Couret.InterIA.SingletonNecessity.p2m_local_matching_rows_zero.match_1.{1}
                    (fun x => Couret.InterIA.SingletonNecessity.Vec) x fun v j =>
                    @HSub.hSub.{0, 0, 0} Couret.InterIA.SingletonNecessity.Vec Couret.InterIA.SingletonNecessity.Vec
                      Couret.InterIA.SingletonNecessity.Vec
                      (@instHSub.{0} Couret.InterIA.SingletonNecessity.Vec
                        (@Pi.instSub.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                          (fun a => Int) fun i => Int.instSub))
                      v
                      (@GetElem?.getElem!.{0, 0, 0} (List.{0} Couret.InterIA.SingletonNecessity.Vec) Nat
                        Couret.InterIA.SingletonNecessity.Vec
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} Couret.InterIA.SingletonNecessity.Vec as))
                        (@List.instGetElem?NatLtLength.{0} Couret.InterIA.SingletonNecessity.Vec)
                        (@Pi.instInhabited.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                          (fun a => Int) fun a => Int.instInhabited)
                        R j))
                (@List.zip.{0, 0} Couret.InterIA.SingletonNecessity.Vec Nat L p))
              v →
            @Eq.{p2m_u_0 + 1} G
              (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
                (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
                  (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
                    (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                Couret.InterIA.SingletonNecessity.Vec (fun x => G)
                (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
                  (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
                    (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                (@Couret.InterIA.SingletonNecessity.evaluation.{p2m_u_0} G inst x) v)
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_matching_rows_zero

