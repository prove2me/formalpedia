-- Prove2me | solution 1 for Couret.mod30_run_for_factorization
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:37:57.0962+00:00
-- url     : https://prove2.me/submissions/81fc5113-7161-4e09-a4d0-9f0e05f2dd8a

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_properSupport_mod30_iff_divisor
import Theorems.Thm_Couret_residue30_injective
import Theorems.Thm_Couret_run_correct
import Definitions.Def_Couret_DivisorCompleteness_e4011d047800

/-!
COU-87 S2M, 2026-10-30: the exact bridge from natural divisors to the
eight-letter modulo-30 automaton. Prime occurrences need not be distinct.
No finite 147-state / 101-class table is imported here.
-/

universe v
namespace Couret



namespace Choice











end Choice













theorem coprime30Factors_of_total (w : Word Nat)
    (hw : Nat.gcd (total natProduct w) 30 = 1) : w.coprime30Factors := by
  induction w with
  | empty => exact True.intro
  | snoc w p ih =>
    have htail : total natProduct w ∣ total natProduct (.snoc w p) := ⟨p, rfl⟩
    have hlast : p ∣ total natProduct (.snoc w p) := by
      refine ⟨total natProduct w, ?_⟩
      exact Nat.mul_comm _ _
    exact ⟨ih (coprime30_of_dvd htail hw), coprime30_of_dvd hlast hw⟩

theorem total_map_residue (w : Word Nat) (hw : w.coprime30Factors) :
    residue30 (total mod30Product (w.map encode30)) = (total natProduct w) % 30 := by
  induction w with
  | empty => rfl
  | snoc w p ih =>
    change residue30 (mul30 (total mod30Product (w.map encode30)) (encode30 p)) =
      (total natProduct w * p) % 30
    rw [mul30_residue, ih hw.1, decode_encode30 p hw.2]
    exact (Nat.mul_mod _ _ _).symm



theorem total_map_eq_encode (w : Word Nat)
    (hw : Nat.gcd (total natProduct w) 30 = 1) :
    total mod30Product (w.map encode30) = encode30 (total natProduct w) := by
  apply residue30_injective
  rw [total_map_residue w (coprime30Factors_of_total w hw), decode_encode30 _ hw]









theorem mod30_run_exact_divisor_semantics (w : Word Nat) (hp : w.primeFactors)
    (hc : Nat.gcd (total natProduct w) 30 = 1) (hne : w.nonempty) :
    run mod30Product (w.map encode30) =
      State.active (encode30 (total natProduct w)) (fun u =>
        ∃ d : Nat, d ∣ total natProduct w ∧ 1 < d ∧ d < total natProduct w ∧
          d % 30 = residue30 u) := by
  rw [run_correct]
  cases w with
  | empty => exact False.elim hne
  | snoc w p =>
    change State.active (total mod30Product ((Word.snoc w p).map encode30))
      (properSupport mod30Product ((Word.snoc w p).map encode30)) = _
    rw [total_map_eq_encode (.snoc w p) hc]
    apply congrArg (State.active (encode30 (total natProduct (.snoc w p))))
    funext u
    exact propext (properSupport_mod30_iff_divisor (.snoc w p) hp hc u)



theorem p2m_local_mod30_run_for_factorization (w : Word Nat) (hp : w.primeFactors)
    (n : Nat) (hn : total natProduct w = n) (hc : Nat.gcd n 30 = 1) (h1 : 1 < n) :
    run mod30Product (w.map encode30) = State.active (encode30 n) (fun u =>
      ∃ d : Nat, d ∣ n ∧ 1 < d ∧ d < n ∧ d % 30 = residue30 u) := by
  have hne : w.nonempty := by
    cases w with
    | empty => change 1 = n at hn; omega
    | snoc _ _ => exact True.intro
  have hc' : Nat.gcd (total natProduct w) 30 = 1 := hn.symm ▸ hc
  have he := mod30_run_exact_divisor_semantics w hp hc' hne
  rw [hn] at he
  exact he







end Couret


theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.primeFactors w →
    ∀ (n : Nat),
      @Eq.{1} Nat (@Couret.total.{0} Nat Couret.natProduct w) n →
        @Eq.{1} Nat (Nat.gcd n (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
            @Eq.{1} (Couret.State.{0} Couret.Code30)
              (@Couret.run.{0} Couret.Code30 Couret.mod30Product
                (@Couret.Word.map.{0} Nat Couret.Code30 Couret.encode30 w))
              (@Couret.State.active.{0} Couret.Code30 (Couret.encode30 n) fun u =>
                @Exists.{1} Nat fun d =>
                  And (@Dvd.dvd.{0} Nat Nat.instDvd d n)
                    (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
                      (And (@LT.lt.{0} Nat instLTNat d n)
                        (@Eq.{1} Nat
                          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) d
                            (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                          (Couret.residue30 u))))) := @_root_.Couret.p2m_local_mod30_run_for_factorization

