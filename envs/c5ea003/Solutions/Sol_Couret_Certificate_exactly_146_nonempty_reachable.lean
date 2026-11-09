-- Prove2me | solution 1 for Couret.Certificate.exactly_146_nonempty_reachable
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:51.268637+00:00
-- url     : https://prove2.me/submissions/fe8bf32b-e034-4224-962b-aa16431a9c5e

import Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
import Std
import Theorems.Thm_Couret_Certificate_StepValid_sound
import Theorems.Thm_Couret_Certificate_decode_injective
import Theorems.Thm_Couret_Certificate_entry_injective
import Theorems.Thm_Couret_Certificate_initial_encoding
import Theorems.Thm_Couret_Certificate_nonempty_witness_checked
import Theorems.Thm_Couret_Certificate_reachability_checked
import Theorems.Thm_Couret_Certificate_symbol_code
import Theorems.Thm_Couret_Certificate_transitions_checked
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate



theorem decoded_injective {i j : StateId} (h : decoded i = decoded j) : i = j :=
  entry_injective i j (decode_injective h)

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

theorem map_nonempty {α β : Type} (f : α → β) (w : Word α) :
    (w.map f).nonempty ↔ w.nonempty := by cases w <;> rfl







theorem tableNext_noninitial (i : StateId) (g : Symbol) : tableNext i g ≠ 0 := by
  intro h
  have hc := transitions_checked i g
  rw [h, initial_encoding] at hc
  cases he : entry i <;> simp [he, StepValid] at hc

theorem nonempty_run_noninitial (w : Word Symbol) (hw : w.nonempty) :
    tableRun 0 w ≠ 0 := by
  cases w with
  | empty => exact False.elim hw
  | snoc w g => exact tableNext_noninitial (tableRun 0 w) g



theorem p2m_local_exactly_146_nonempty_reachable :
    (∀ i j : Fin 146, noninitialDecoded i = noninitialDecoded j → i = j) ∧
    (∀ s : State Code30,
      (∃ w : Word Code30, w.nonempty ∧ run mod30Product w = s) ↔
        ∃ i : Fin 146, noninitialDecoded i = s) := by
  constructor
  · intro i j h
    have he : i.succ = j.succ := decoded_injective h
    exact Fin.succ_inj.mp he
  · intro s
    constructor
    · rintro ⟨w, hw, hr⟩
      let i := tableRun 0 (w.map codeSymbol)
      have hi : i ≠ 0 := nonempty_run_noninitial _ ((map_nonempty codeSymbol w).mpr hw)
      have hs : decoded i = s := by
        change decoded (tableRun 0 (w.map codeSymbol)) = s
        rw [tableRun_sound, word_codes_symbols, hr]
      have hpos : 0 < i.val := by
        have hz : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      let j : Fin 146 := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hj : j.succ = i := by
        apply Fin.ext
        change (i.val - 1) + 1 = i.val
        omega
      refine ⟨j, ?_⟩
      change decoded j.succ = s
      rw [hj]
      exact hs
    · rintro ⟨i, rfl⟩
      refine ⟨(reachWord i.succ).map symbolCode, ?_, ?_⟩
      · apply (map_nonempty symbolCode _).mpr
        exact nonempty_witness_checked i.succ (Fin.succ_ne_zero i)
      · rw [← tableRun_sound, reachability_checked]; rfl





















































end Certificate
end Couret

theorem solution : And
  (∀ (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))),
    @Eq.{1} (Couret.State.{0} Couret.Code30) (Couret.Certificate.noninitialDecoded i)
        (Couret.Certificate.noninitialDecoded j) →
      @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))) i j)
  (∀ (s : Couret.State.{0} Couret.Code30),
    Iff
      (@Exists.{1} (Couret.Word.{0} Couret.Code30) fun w =>
        And (@Couret.Word.nonempty.{0} Couret.Code30 w)
          (@Eq.{1} (Couret.State.{0} Couret.Code30) (@Couret.run.{0} Couret.Code30 Couret.mod30Product w) s))
      (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))) fun i =>
        @Eq.{1} (Couret.State.{0} Couret.Code30) (Couret.Certificate.noninitialDecoded i) s)) := @_root_.Couret.Certificate.p2m_local_exactly_146_nonempty_reachable

