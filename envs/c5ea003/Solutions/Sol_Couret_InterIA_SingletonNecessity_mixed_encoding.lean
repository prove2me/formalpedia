-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.mixed_encoding
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:22.925204+00:00
-- url     : https://prove2.me/submissions/71220ee8-9a40-486d-af0d-c30192049e15

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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_basis
import Theorems.Thm_Couret_InterIA_SingletonNecessity_matching_rows_zero
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem evaluated_terms (x : Fin 6 → G) :
    leftTerms.map (evaluation x)=sumTermsLeft x ∧
    rightTerms.map (evaluation x)=sumTermsRight x := by
  have e0 : evaluation x (basis 0)=x 0 := evaluation_basis x (0:Fin 6)
  have e1 : evaluation x (basis 1)=x 1 := evaluation_basis x (1:Fin 6)
  have e2 : evaluation x (basis 2)=x 2 := evaluation_basis x (2:Fin 6)
  have e3 : evaluation x (basis 3)=x 3 := evaluation_basis x (3:Fin 6)
  have e4 : evaluation x (basis 4)=x 4 := evaluation_basis x (4:Fin 6)
  have e5 : evaluation x (basis 5)=x 5 := evaluation_basis x (5:Fin 6)
  constructor <;> simp only [leftTerms,rightTerms,sumTermsLeft,sumTermsRight,
    List.map_cons,List.map_nil,map_add,e0,e1,e2,e3,e4,e5]





theorem p2m_local_mixed_encoding (x : Fin 6 → G) (hx : MixedDoubles x)
    (hp : (sumTermsLeft x ++ [x 0+x 0]).Perm (sumTermsRight x ++ [x 3+x 3])) :
    ∃ p : List ℕ, p.Perm (List.range 7) ∧
      ∀ v ∈ relations true p, evaluation x v=0 := by
  have he := evaluated_terms x
  have e0 : evaluation x (basis 0)=x 0 := evaluation_basis x (0:Fin 6)
  have e1 : evaluation x (basis 1)=x 1 := evaluation_basis x (1:Fin 6)
  have e2 : evaluation x (basis 2)=x 2 := evaluation_basis x (2:Fin 6)
  have e3 : evaluation x (basis 3)=x 3 := evaluation_basis x (3:Fin 6)
  have e4 : evaluation x (basis 4)=x 4 := evaluation_basis x (4:Fin 6)
  have e5 : evaluation x (basis 5)=x 5 := evaluation_basis x (5:Fin 6)
  obtain ⟨p,hp,hr⟩ := matching_rows_zero x
    (leftTerms++[(2:ℤ) • basis 0]) (rightTerms++[(2:ℤ) • basis 3]) (by
      simpa only [List.map_append,List.map_cons,List.map_nil,map_zsmul,map_add,
        e0,e3,two_zsmul,he.1,he.2] using hp)
  refine ⟨p,by simpa [rightTerms] using hp,?_⟩
  rcases hx with ⟨h0,h1,h2⟩
  intro v hv
  simp only [relations,if_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with (rfl|rfl|rfl)|hv
  · simp only [map_add,map_sub,e0,e1,two_zsmul]
    calc
      (x 0-x 1)+(x 0-x 1)=(x 0+x 0)-(x 1+x 1) := by abel
      _ = 0 := sub_eq_zero.mpr h0
  · simp only [map_add,map_sub,e3,e4,two_zsmul]
    calc
      (x 3-x 4)+(x 3-x 4)=(x 3+x 3)-(x 4+x 4) := by abel
      _ = 0 := sub_eq_zero.mpr h1
  · simp only [map_add,map_sub,e2,e5,two_zsmul]
    calc
      (x 2-x 5)+(x 2-x 5)=(x 2+x 2)-(x 5+x 5) := by abel
      _ = 0 := sub_eq_zero.mpr h2
  · exact hr v hv

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.MixedDoubles.{p2m_u_0} G inst x →
    @List.Perm.{p2m_u_0} G
        (@HAppend.hAppend.{p2m_u_0, p2m_u_0, p2m_u_0} (List.{p2m_u_0} G) (List.{p2m_u_0} G) (List.{p2m_u_0} G)
          (@instHAppendOfAppend.{p2m_u_0} (List.{p2m_u_0} G) (@List.instAppend.{p2m_u_0} G))
          (@Couret.InterIA.SingletonNecessity.sumTermsLeft.{p2m_u_0} G inst x)
          (@List.cons.{p2m_u_0} G
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 0)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 0))))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 0)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 0)))))
            (@List.nil.{p2m_u_0} G)))
        (@HAppend.hAppend.{p2m_u_0, p2m_u_0, p2m_u_0} (List.{p2m_u_0} G) (List.{p2m_u_0} G) (List.{p2m_u_0} G)
          (@instHAppendOfAppend.{p2m_u_0} (List.{p2m_u_0} G) (@List.instAppend.{p2m_u_0} G))
          (@Couret.InterIA.SingletonNecessity.sumTermsRight.{p2m_u_0} G inst x)
          (@List.cons.{p2m_u_0} G
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 3)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 3))))
              (x
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 3)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 3)))))
            (@List.nil.{p2m_u_0} G))) →
      @Exists.{1} (List.{0} Nat) fun p =>
        And (@List.Perm.{0} Nat p (List.range (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
          (∀ (v : Couret.InterIA.SingletonNecessity.Vec),
            @Membership.mem.{0, 0} Couret.InterIA.SingletonNecessity.Vec
                (List.{0} Couret.InterIA.SingletonNecessity.Vec)
                (@List.instMembership.{0} Couret.InterIA.SingletonNecessity.Vec)
                (Couret.InterIA.SingletonNecessity.relations Bool.true p) v →
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
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_mixed_encoding

