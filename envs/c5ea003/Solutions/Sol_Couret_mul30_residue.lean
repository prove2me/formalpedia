-- Prove2me | solution 1 for Couret.mul30_residue
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:13.029933+00:00
-- url     : https://prove2.me/submissions/ab764a3b-d4b3-4617-8296-7127290c53c4

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
















theorem p2m_local_mul30_residue : ∀ a b : Code30,
    residue30 (mul30 a b) = (residue30 a * residue30 b) % 30 := by decide









end Couret


theorem solution : ∀ (a b : Couret.Code30),
  @Eq.{1} Nat (Couret.residue30 (Couret.mul30 a b))
    (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (Couret.residue30 a) (Couret.residue30 b))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := @_root_.Couret.p2m_local_mul30_residue

