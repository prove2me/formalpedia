-- Prove2me | solution 1 for Couret.S5.five_proper_divisor_residues
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:30.935206+00:00
-- url     : https://prove2.me/submissions/24ec4ec0-f5e7-488f-b615-475396c5b7ae

import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
import Std
import Theorems.Thm_Couret_maskRun_correct
import Theorems.Thm_Couret_mask_254_omits_only_residue_one
import Theorems.Thm_Couret_properSupport_mod30_iff_divisor
import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5




theorem five_product : total natProduct fivePrimes = 64141 := by decide +kernel

theorem prime_from_bounded (p : Nat) (hp : 2 ≤ p)
    (hd : ∀ d : Fin (p+1), d.val ∣ p → d.val = 1 ∨ d.val = p) : PrimeNat p := by
  refine ⟨hp,?_⟩
  intro d h
  have hle : d ≤ p := Nat.le_of_dvd (by omega) h
  exact hd ⟨d,by omega⟩ h

theorem prime_seven : PrimeNat 7 := prime_from_bounded 7 (by decide) (by decide +kernel)
theorem prime_eleven : PrimeNat 11 := prime_from_bounded 11 (by decide) (by decide +kernel)
theorem prime_seventeen : PrimeNat 17 := prime_from_bounded 17 (by decide) (by decide +kernel)

theorem five_primeFactors : fivePrimes.primeFactors :=
  ⟨⟨⟨⟨⟨True.intro,prime_seven⟩,prime_seven⟩,prime_seven⟩,prime_eleven⟩,prime_seventeen⟩

theorem five_coprime : Nat.gcd (total natProduct fivePrimes) 30 = 1 := by decide +kernel

theorem five_mask : maskRun (fivePrimes.map encode30) = MaskState.active (0,0) 254 := by decide +kernel

theorem five_proper_support (u : Code30) :
    properSupport mod30Product (fivePrimes.map encode30) u ↔ residue30 u ≠ 1 := by
  have he := maskRun_correct (fivePrimes.map encode30)
  rw [five_mask] at he
  change State.active (0,0) (maskSupport 254) =
    State.active (total mod30Product (fivePrimes.map encode30))
      (properSupport mod30Product (fivePrimes.map encode30)) at he
  have hs := (State.active.inj he).2
  exact (Iff.of_eq (congrFun hs u)).symm.trans (mask_254_omits_only_residue_one u)







theorem p2m_local_five_proper_divisor_residues (u : Code30) :
    (∃ d : Nat, d ∣ 64141 ∧ 1 < d ∧ d < 64141 ∧ d % 30 = residue30 u) ↔ residue30 u ≠ 1 := by
  have hi := properSupport_mod30_iff_divisor fivePrimes five_primeFactors five_coprime u
  rw [five_product] at hi
  exact hi.symm.trans (five_proper_support u)











end S5
end Couret

theorem solution : ∀ (u : Couret.Code30),
  Iff
    (@Exists.{1} Nat fun d =>
      And (@Dvd.dvd.{0} Nat Nat.instDvd d (@OfNat.ofNat.{0} Nat (nat_lit 64141) (instOfNatNat (nat_lit 64141))))
        (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
          (And (@LT.lt.{0} Nat instLTNat d (@OfNat.ofNat.{0} Nat (nat_lit 64141) (instOfNatNat (nat_lit 64141))))
            (@Eq.{1} Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) d
                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
              (Couret.residue30 u)))))
    (@Ne.{1} Nat (Couret.residue30 u) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @_root_.Couret.S5.p2m_local_five_proper_divisor_residues

