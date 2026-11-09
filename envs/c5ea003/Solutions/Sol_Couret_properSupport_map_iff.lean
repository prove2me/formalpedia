-- Prove2me | solution 1 for Couret.properSupport_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:20.677714+00:00
-- url     : https://prove2.me/submissions/eb118254-b34b-434b-8150-480b05250bb9

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_residue30_injective
import Definitions.Def_Couret_DivisorCompleteness_e4011d047800

/-!
COU-87 S2M, 2026-10-30: the exact bridge from natural divisors to the
eight-letter modulo-30 automaton. Prime occurrences need not be distinct.
No finite 147-state / 101-class table is imported here.
-/

universe v
namespace Couret



namespace Choice





theorem map_pullback {α : Type v} {β : Type v} (f : α → β)
    (w : Word α) (s : Choice (w.map f)) : map f (pullback f w s) = s := by
  induction w with
  | empty => cases s; rfl
  | snoc w g ih =>
    cases s with
    | skip s => exact congrArg (fun t => skip t (f g)) (ih s)
    | take s => exact congrArg (fun t => take t (f g)) (ih s)

theorem picked_map {α : Type v} {β : Type v} (f : α → β)
    {w : Word α} (s : Choice w) : picked (map f s) ↔ picked s := by
  induction s with
  | empty => rfl
  | skip s g ih => exact ih
  | take s g ih => rfl

theorem omitted_map {α : Type v} {β : Type v} (f : α → β)
    {w : Word α} (s : Choice w) : omitted (map f s) ↔ omitted s := by
  induction s with
  | empty => rfl
  | skip s g ih => rfl
  | take s g ih => exact ih

end Choice

















theorem eval_map_residue {w : Word Nat} (s : Choice w) (hw : w.coprime30Factors) :
    residue30 (Choice.eval mod30Product (s.map encode30)) =
      (Choice.eval natProduct s) % 30 := by
  induction s with
  | empty => rfl
  | skip s p ih => exact ih hw.1
  | take s p ih =>
    change residue30 (mul30 (Choice.eval mod30Product (s.map encode30)) (encode30 p)) =
      (Choice.eval natProduct s * p) % 30
    rw [mul30_residue, ih hw.1, decode_encode30 p hw.2]
    exact (Nat.mul_mod _ _ _).symm





theorem p2m_local_properSupport_map_iff (w : Word Nat) (hw : w.coprime30Factors) (u : Code30) :
    properSupport mod30Product (w.map encode30) u ↔
      ∃ d : Nat, properSupport natProduct w d ∧ d % 30 = residue30 u := by
  constructor
  · rintro ⟨t, hp, ho, ht⟩
    let s := Choice.pullback encode30 w t
    have hm : s.map encode30 = t := Choice.map_pullback encode30 w t
    have hps : s.picked := (Choice.picked_map encode30 s).mp (hm.symm ▸ hp)
    have hos : s.omitted := (Choice.omitted_map encode30 s).mp (hm.symm ▸ ho)
    have he := eval_map_residue s hw
    rw [hm, ht] at he
    exact ⟨Choice.eval natProduct s, ⟨s, hps, hos, rfl⟩, he.symm⟩
  · rintro ⟨d, ⟨s, hp, ho, hs⟩, hd⟩
    refine ⟨s.map encode30, (Choice.picked_map encode30 s).mpr hp,
      (Choice.omitted_map encode30 s).mpr ho, ?_⟩
    apply residue30_injective
    rw [eval_map_residue s hw, hs]
    exact hd

















end Couret


theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.coprime30Factors w →
    ∀ (u : Couret.Code30),
      Iff
        (@Couret.properSupport.{0} Couret.Code30 Couret.mod30Product
          (@Couret.Word.map.{0} Nat Couret.Code30 Couret.encode30 w) u)
        (@Exists.{1} Nat fun d =>
          And (@Couret.properSupport.{0} Nat Couret.natProduct w d)
            (@Eq.{1} Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) d
                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
              (Couret.residue30 u))) := @_root_.Couret.p2m_local_properSupport_map_iff

