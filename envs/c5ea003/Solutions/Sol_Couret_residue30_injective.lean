-- Prove2me | solution 1 for Couret.residue30_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:51:45.410177+00:00
-- url     : https://prove2.me/submissions/bfc5656b-7061-4e25-bff8-7ffcd5993b92

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
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







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


















theorem p2m_local_residue30_injective : ∀ a b : Code30,
    residue30 a = residue30 b → a = b := by decide







end Couret


theorem solution : ∀ (a b : Couret.Code30), @Eq.{1} Nat (Couret.residue30 a) (Couret.residue30 b) → @Eq.{1} Couret.Code30 a b := @_root_.Couret.p2m_local_residue30_injective

