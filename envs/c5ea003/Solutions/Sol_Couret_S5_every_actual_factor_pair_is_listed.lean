-- Prove2me | solution 1 for Couret.S5.every_actual_factor_pair_is_listed
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:51:49.770953+00:00
-- url     : https://prove2.me/submissions/36945567-9038-4d81-8b33-ccb30ebf75c8

import Definitions.Def_Couret_FivePairSemantics_d40383365465
import Std
import Theorems.Thm_Couret_S5_five_factorPair_exact
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_decode_encode30
import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
namespace Couret
namespace S5

/- The cancellation/complement argument follows the archived S4 proof,
   specialized here to the explicit five-prime counterexample. -/










theorem five_pairList_membership : ∀ a b : Code30,
    (residue30 a,residue30 b) ∈ pairList (0,0) 254 ↔ maskPair64141 a b := by
  unfold maskPair64141
  decide +kernel

theorem five_pairList_exact (a b : Code30) :
    (residue30 a,residue30 b) ∈ pairList (0,0) 254 ↔ factorPair64141 a b :=
  (five_pairList_membership a b).trans (five_factorPair_exact a b).symm



theorem p2m_local_every_actual_factor_pair_is_listed (d e : Nat) (hd : 1 < d) (he : 1 < e)
    (hprod : d * e = 64141) :
    (d % 30,e % 30) ∈ pairList (0,0) 254 ∨
      (e % 30,d % 30) ∈ pairList (0,0) 254 := by
  have hcd := coprime30_of_dvd (show d ∣ 64141 from ⟨e,hprod.symm⟩)
    (by decide : Nat.gcd 64141 30 = 1)
  have hce := coprime30_of_dvd (show e ∣ 64141 from ⟨d,hprod.symm.trans (Nat.mul_comm d e)⟩)
    (by decide : Nat.gcd 64141 30 = 1)
  by_cases hab : bitIndex30 (encode30 d) ≤ bitIndex30 (encode30 e)
  · have hp : factorPair64141 (encode30 d) (encode30 e) :=
      ⟨d,e,hd,he,hprod,(decode_encode30 d hcd).symm,(decode_encode30 e hce).symm,hab⟩
    have hh := (five_pairList_exact _ _).mpr hp
    exact Or.inl (by simpa only [decode_encode30 d hcd,decode_encode30 e hce] using hh)
  · have hba : bitIndex30 (encode30 e) ≤ bitIndex30 (encode30 d) := by omega
    have hp : factorPair64141 (encode30 e) (encode30 d) :=
      ⟨e,d,he,hd,(Nat.mul_comm e d).trans hprod,
        (decode_encode30 e hce).symm,(decode_encode30 d hcd).symm,hba⟩
    have hh := (five_pairList_exact _ _).mpr hp
    exact Or.inr (by simpa only [decode_encode30 e hce,decode_encode30 d hcd] using hh)

end S5
end Couret

theorem solution : ∀ (d e : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) e →
      @Eq.{1} Nat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d e)
          (@OfNat.ofNat.{0} Nat (nat_lit 64141) (instOfNatNat (nat_lit 64141))) →
        Or
          (@Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
            (@List.instMembership.{0} (Prod.{0, 0} Nat Nat))
            (Couret.S5.pairList
              (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0))))
              (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254))))
            (@Prod.mk.{0, 0} Nat Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) d
                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) e
                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))
          (@Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
            (@List.instMembership.{0} (Prod.{0, 0} Nat Nat))
            (Couret.S5.pairList
              (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0))))
              (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254))))
            (@Prod.mk.{0, 0} Nat Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) e
                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) d
                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))) := @_root_.Couret.S5.p2m_local_every_actual_factor_pair_is_listed

