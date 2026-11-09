-- Prove2me | Theorems.Thm_Couret_Choice_eval_mul_complement
-- name    : Couret.Choice.eval_mul_complement
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:37.83124+00:00
-- url     : https://prove2.me/theorems/5a7c051e-c9b6-4f71-83b3-5ca82574ac5d
-- title:
--   A selection and its complement recover the total product
-- statement:
--   Let $M$ be a commutative monoid on a type $A$, $w$ a finite word over $A$, and $P(w)$ its total product. A selection chooses positions of $w$; a proper selection chooses at least one position and omits at least one. For every selection $s$ of $w$,
--
--   $$\operatorname{prod}(s)\operatorname{prod}(s^{\mathrm c})=P(w).$$
--
--   The result includes empty words and empty selections, whose products are the identity.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 123–139; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.Choice.eval_mul_complement

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

theorem eval_mul_complement (M : CMonoid α) {w : Word α} (s : Choice w) :
    M.mul (eval M s) (eval M (complement s)) = total M w := by sorry


end Choice







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
