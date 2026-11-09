-- Prove2me | solution 1 for Couret.S5.five_factorPair_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:39.733515+00:00
-- url     : https://prove2.me/submissions/16e84b1d-016e-4384-a2b3-404f980aca5f

import Definitions.Def_Couret_FivePairSemantics_d40383365465
import Std
import Theorems.Thm_Couret_S5_five_proper_divisor_residues
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mask_254_omits_only_residue_one
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_residue30_injective
import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
namespace Couret
namespace S5

/- The cancellation/complement argument follows the archived S4 proof,
   specialized here to the explicit five-prime counterexample. -/




theorem code_left_cancel : ∀ a b c : Code30, mul30 a b = mul30 a c → b = c := by decide +kernel



theorem p2m_local_five_factorPair_exact (a b : Code30) : factorPair64141 a b ↔ maskPair64141 a b := by
  constructor
  · rintro ⟨d,e,hd,he,hden,hrd,hre,hab⟩
    have hdlt : d < 64141 := by
      have hh : d * 2 ≤ 64141 := by
        calc
          d * 2 ≤ d * e := Nat.mul_le_mul_left d (by omega)
          _ = 64141 := hden
      omega
    have helt : e < 64141 := by
      have hh : e * 2 ≤ 64141 := by
        calc
          e * 2 ≤ e * d := Nat.mul_le_mul_left e (by omega)
          _ = 64141 := (Nat.mul_comm e d).trans hden
      omega
    have hda := (five_proper_divisor_residues a).mp ⟨d,⟨e,hden.symm⟩,hd,hdlt,hrd⟩
    have heb := (five_proper_divisor_residues b).mp ⟨e,⟨d,hden.symm.trans (Nat.mul_comm d e)⟩,he,helt,hre⟩
    refine ⟨hab,(mask_254_omits_only_residue_one a).mpr hda,
      (mask_254_omits_only_residue_one b).mpr heb,?_⟩
    apply residue30_injective
    rw [mul30_residue,← hrd,← hre,← Nat.mul_mod,hden]
    decide
  · rintro ⟨hab,hma,_,hprod⟩
    rcases (five_proper_divisor_residues a).mpr ((mask_254_omits_only_residue_one a).mp hma) with ⟨d,hdiv,hd,hdlt,hrd⟩
    rcases hdiv with ⟨e,hden⟩
    have he0 : e ≠ 0 := by intro h; rw [h,Nat.mul_zero] at hden; omega
    have he1 : e ≠ 1 := by intro h; rw [h,Nat.mul_one] at hden; omega
    have he : 1 < e := by omega
    have hed : e ∣ 64141 := ⟨d,hden.trans (Nat.mul_comm d e)⟩
    have hce := coprime30_of_dvd hed (by decide : Nat.gcd 64141 30 = 1)
    have hmul : mul30 a (encode30 e) = (0,0) := by
      apply residue30_injective
      rw [mul30_residue,decode_encode30 e hce,← hrd,← Nat.mul_mod,← hden]
      decide
    have heb : encode30 e = b := code_left_cancel a _ _ (hmul.trans hprod.symm)
    have heres : e % 30 = residue30 b := by
      have hh := congrArg residue30 heb
      simpa only [decode_encode30 e hce] using hh
    exact ⟨d,e,hd,he,hden.symm,hrd,heres,hab⟩









end S5
end Couret

theorem solution : ∀ (a b : Couret.Code30), Iff (Couret.S5.factorPair64141 a b) (Couret.S5.maskPair64141 a b) := @_root_.Couret.S5.p2m_local_five_factorPair_exact

