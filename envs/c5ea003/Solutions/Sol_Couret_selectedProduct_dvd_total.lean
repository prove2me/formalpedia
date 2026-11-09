-- Prove2me | solution 1 for Couret.selectedProduct_dvd_total
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:29.485386+00:00
-- url     : https://prove2.me/submissions/6f125904-a25a-41c1-be00-795eb3eed691

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_Choice_eval_mul_complement
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



























theorem p2m_local_selectedProduct_dvd_total {w : Word Nat} (s : Choice w) :
    Choice.eval natProduct s ∣ total natProduct w := by
  exact ⟨Choice.eval natProduct (Choice.complement s),
    (Choice.eval_mul_complement natProduct s).symm⟩











/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


theorem solution : ∀ {w : Couret.Word.{0} Nat} (s : @Couret.Choice.{0} Nat w),
  @Dvd.dvd.{0} Nat Nat.instDvd (@Couret.Choice.eval.{0} Nat Couret.natProduct w s)
    (@Couret.total.{0} Nat Couret.natProduct w) := @_root_.Couret.p2m_local_selectedProduct_dvd_total

