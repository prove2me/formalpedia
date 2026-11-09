-- Prove2me | solution 1 for Couret.Certificate.factorization_T_certificate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:12.594392+00:00
-- url     : https://prove2.me/submissions/8aacbf08-d974-4c1a-ac7c-ad57293b5b1f

import Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
import Std
import Theorems.Thm_Couret_Certificate_StepValid_sound
import Theorems.Thm_Couret_Certificate_initial_encoding
import Theorems.Thm_Couret_Certificate_observation_checked
import Theorems.Thm_Couret_Certificate_pairPresent_semantics
import Theorems.Thm_Couret_Certificate_symbol_code
import Theorems.Thm_Couret_Certificate_transitions_checked
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mod30_run_for_factorization
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_residue30_injective
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate





theorem tableNext_semantic (i : StateId) (g : Symbol) :
    decoded (tableNext i g) = step mod30Product (decoded i) (symbolCode g) :=
  StepValid_sound (transitions_checked i g)

theorem tableRun_sound (w : Word Symbol) :
    decoded (tableRun 0 w) = run mod30Product (w.map symbolCode) := by
  induction w with
  | empty => change decode (entry 0) = State.initial; rw [initial_encoding]; rfl
  | snoc w g ih =>
    change decoded (tableNext (tableRun 0 w) g) =
      step mod30Product (run mod30Product (w.map symbolCode)) (symbolCode g)
    rw [tableNext_semantic, ih]

theorem word_codes_symbols (w : Word Code30) :
    (w.map codeSymbol).map symbolCode = w := by
  induction w with
  | empty => rfl
  | snoc w g ih =>
    change Word.snoc ((w.map codeSymbol).map symbolCode) (symbolCode (codeSymbol g)) = .snoc w g
    rw [ih, symbol_code]



theorem every_run_in_table (w : Word Code30) :
    ∃ i : StateId, decoded i = run mod30Product w := by
  refine ⟨tableRun 0 (w.map codeSymbol), ?_⟩
  rw [tableRun_sound, word_codes_symbols]













theorem table_T_is_presence_count (i : StateId) :
    tableOutput i = presenceCount (entry i) := (observation_checked i).2

theorem table_T_is_mask_formula (i : StateId) :
    tableOutput i = outputMask (entry i) := (observation_checked i).1

theorem pairPresent_decoded (s : EncodedState) (a b : Symbol) :
    pairPresent s a b = true ↔ match decode s with
      | .initial => False
      | .active r U => U (symbolCode a) ∧ U (symbolCode b) ∧ a.val ≤ b.val ∧
          mul30 (symbolCode a) (symbolCode b) = r := by
  cases s with
  | none => simp [pairPresent, decode]
  | some s => exact pairPresent_semantics s.1 s.2 a b





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







theorem p2m_local_factorization_T_certificate (w : Word Nat) (hp : w.primeFactors)
    (n : Nat) (hn : total natProduct w = n) (hc : Nat.gcd n 30 = 1) (h1 : 1 < n) :
    ∃ i : StateId,
      decoded i = State.active (encode30 n) (strictDivisorResidue n) ∧
      tableOutput i = presenceCount (entry i) ∧
      tableOutput i = outputMask (entry i) ∧
      ∀ a b : Symbol, pairPresent (entry i) a b = true ↔ arithmeticPair n a b := by
  rcases every_run_in_table (w.map encode30) with ⟨i, hi⟩
  have he := mod30_run_for_factorization w hp n hn hc h1
  have hs : decoded i = State.active (encode30 n) (strictDivisorResidue n) := hi.trans he
  refine ⟨i, hs, table_T_is_presence_count i, table_T_is_mask_formula i, ?_⟩
  intro a b
  rw [pairPresent_decoded]
  change decode (entry i) = State.active (encode30 n) (strictDivisorResidue n) at hs
  rw [hs]
  change (strictDivisorResidue n (symbolCode a) ∧ strictDivisorResidue n (symbolCode b) ∧
    a.val ≤ b.val ∧ mul30 (symbolCode a) (symbolCode b) = encode30 n) ↔ arithmeticPair n a b
  simp only [arithmeticPair, coded_product_iff n hc a b]

































end Certificate
end Couret

theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.primeFactors w →
    ∀ (n : Nat),
      @Eq.{1} Nat (@Couret.total.{0} Nat Couret.natProduct w) n →
        @Eq.{1} Nat (Nat.gcd n (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
            @Exists.{1} Couret.Certificate.StateId fun i =>
              And
                (@Eq.{1} (Couret.State.{0} Couret.Code30) (Couret.Certificate.decoded i)
                  (@Couret.State.active.{0} Couret.Code30 (Couret.encode30 n)
                    (Couret.Certificate.strictDivisorResidue n)))
                (And
                  (@Eq.{1} Nat (Couret.Certificate.tableOutput i)
                    (Couret.Certificate.presenceCount (Couret.Certificate.entry i)))
                  (And
                    (@Eq.{1} Nat (Couret.Certificate.tableOutput i)
                      (Couret.Certificate.outputMask (Couret.Certificate.entry i)))
                    (∀ (a b : Couret.Certificate.Symbol),
                      Iff (@Eq.{1} Bool (Couret.Certificate.pairPresent (Couret.Certificate.entry i) a b) Bool.true)
                        (Couret.Certificate.arithmeticPair n a b)))) := @_root_.Couret.Certificate.p2m_local_factorization_T_certificate

