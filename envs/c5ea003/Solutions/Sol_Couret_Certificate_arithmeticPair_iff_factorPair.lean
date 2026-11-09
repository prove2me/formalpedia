-- Prove2me | solution 1 for Couret.Certificate.arithmeticPair_iff_factorPair
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:16.467529+00:00
-- url     : https://prove2.me/submissions/ebdabb0d-e487-40f7-b621-a4df90e7c705

import Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
import Std
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_residue30_injective
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate





































theorem coded_product_iff (n : Nat) (hc : Nat.gcd n 30 = 1) (a b : Symbol) :
    mul30 (symbolCode a) (symbolCode b) = encode30 n ↔
      (residue30 (symbolCode a) * residue30 (symbolCode b)) % 30 = n % 30 := by
  constructor
  · intro h
    have he := congrArg residue30 h
    simpa only [mul30_residue, decode_encode30 n hc] using he
  · intro h
    apply residue30_injective
    rw [mul30_residue, decode_encode30 n hc]
    exact h



theorem code_left_cancel : ∀ a b c : Code30, mul30 a b = mul30 a c → b = c := by decide

theorem p2m_local_arithmeticPair_iff_factorPair (n : Nat) (hc : Nat.gcd n 30 = 1) (a b : Symbol) :
    arithmeticPair n a b ↔ factorPair n a b := by
  constructor
  · rintro ⟨⟨d, hdiv, hd1, hdlt, hdres⟩, _, hab, hprod⟩
    rcases hdiv with ⟨e, hden⟩
    have he0 : e ≠ 0 := by intro he; rw [he, Nat.mul_zero] at hden; omega
    have he1 : e ≠ 1 := by intro he; rw [he, Nat.mul_one] at hden; omega
    have he2 : 1 < e := by omega
    have hed : e ∣ n := ⟨d, hden.trans (Nat.mul_comm _ _)⟩
    have hce := coprime30_of_dvd hed hc
    have hmul : mul30 (symbolCode a) (encode30 e) = encode30 n := by
      apply residue30_injective
      rw [mul30_residue, decode_encode30 e hce, decode_encode30 n hc, ← hdres]
      exact (Nat.mul_mod d e 30).symm.trans (congrArg (fun x => x % 30) hden.symm)
    have hmul' := (coded_product_iff n hc a b).mpr hprod
    have heb : encode30 e = symbolCode b := code_left_cancel _ _ _ (hmul.trans hmul'.symm)
    have heres : e % 30 = residue30 (symbolCode b) := by
      have hh := congrArg residue30 heb
      simpa only [decode_encode30 e hce] using hh
    exact ⟨d,e,hd1,he2,hden.symm,hdres,heres,hab⟩
  · rintro ⟨d,e,hd1,he1,hden,hdres,heres,hab⟩
    have hdlt : d < n := by
      have hh : d * 2 ≤ n := by
        calc
          d * 2 ≤ d * e := Nat.mul_le_mul_left d (by omega)
          _ = n := hden
      omega
    have helt : e < n := by
      have hh : e * 2 ≤ n := by
        calc
          e * 2 ≤ e * d := Nat.mul_le_mul_left e (by omega)
          _ = n := (Nat.mul_comm _ _).trans hden
      omega
    have hdiv : d ∣ n := ⟨e,hden.symm⟩
    have hediv : e ∣ n := ⟨d,hden.symm.trans (Nat.mul_comm _ _)⟩
    have hprod : (residue30 (symbolCode a) * residue30 (symbolCode b)) % 30 = n % 30 := by
      rw [← hdres, ← heres, ← Nat.mul_mod, hden]
    exact ⟨⟨d,hdiv,hd1,hdlt,hdres⟩,⟨e,hediv,he1,helt,heres⟩,hab,hprod⟩



































end Certificate
end Couret

theorem solution : ∀ (n : Nat),
  @Eq.{1} Nat (Nat.gcd n (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    ∀ (a b : Couret.Certificate.Symbol),
      Iff (Couret.Certificate.arithmeticPair n a b) (Couret.Certificate.factorPair n a b) := @_root_.Couret.Certificate.p2m_local_arithmeticPair_iff_factorPair

