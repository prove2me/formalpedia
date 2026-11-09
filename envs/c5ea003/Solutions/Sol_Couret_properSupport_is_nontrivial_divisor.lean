-- Prove2me | solution 1 for Couret.properSupport_is_nontrivial_divisor
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:17.481835+00:00
-- url     : https://prove2.me/submissions/ee6c8724-0781-459d-a4cb-fb87307ffa27

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_Choice_eval_mul_complement
import Theorems.Thm_Couret_Choice_picked_complement
import Theorems.Thm_Couret_pickedProduct_gt_one
import Theorems.Thm_Couret_selectedProduct_dvd_total
import Std

/-!
COU-87, first semantic formalization, 2026-10-30.
The denotation uses independent choices of labeled occurrences, not the automaton
recurrence. Snoc words make appending an occurrence explicit. No assumption of
distinct factors is made. This file does not certify the 147/101 finite tables.
-/

universe u
namespace Couret





variable {α : Type u}







namespace Choice

































end Choice





































theorem p2m_local_properSupport_is_nontrivial_divisor (w : Word Nat) (hw : w.atLeastTwo)
    (d : Nat) (h : properSupport natProduct w d) :
    d ∣ total natProduct w ∧ 1 < d ∧ d < total natProduct w := by
  rcases h with ⟨s, hp, ho, rfl⟩
  have hs := pickedProduct_gt_one s hw hp
  have hc := pickedProduct_gt_one (Choice.complement s) hw
    ((Choice.picked_complement s).mpr ho)
  have he := Choice.eval_mul_complement natProduct s
  change Choice.eval natProduct s * Choice.eval natProduct (Choice.complement s) = total natProduct w at he
  have hl : Choice.eval natProduct s * 2 ≤ total natProduct w := by
    calc
      Choice.eval natProduct s * 2 ≤
          Choice.eval natProduct s * Choice.eval natProduct (Choice.complement s) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hc)
      _ = total natProduct w := he
  exact ⟨selectedProduct_dvd_total s, hs, by omega⟩

/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


theorem solution : ∀ (w : Couret.Word.{0} Nat),
  Couret.Word.atLeastTwo w →
    ∀ (d : Nat),
      @Couret.properSupport.{0} Nat Couret.natProduct w d →
        And (@Dvd.dvd.{0} Nat Nat.instDvd d (@Couret.total.{0} Nat Couret.natProduct w))
          (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
            (@LT.lt.{0} Nat instLTNat d (@Couret.total.{0} Nat Couret.natProduct w))) := @_root_.Couret.p2m_local_properSupport_is_nontrivial_divisor

