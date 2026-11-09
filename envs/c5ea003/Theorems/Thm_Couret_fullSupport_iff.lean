-- Prove2me | Theorems.Thm_Couret_fullSupport_iff
-- name    : Couret.fullSupport_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:20.775975+00:00
-- url     : https://prove2.me/theorems/151252aa-1e33-498c-92af-726af421058f
-- title:
--   All subproducts consist of proper subproducts and endpoints
-- statement:
--   Let $M$ be a commutative monoid on a type $A$, $w$ a finite word over $A$, and $P(w)$ its total product. A selection chooses positions of $w$; a proper selection chooses at least one position and omits at least one. For every $u\in A$,
--
--   $$u\in U_{\rm all}(w)\iff u\in U_{\rm proper}(w)\ \lor\ u=1_M\ \lor\ u=P(w).$$
--
--   The statement includes the empty word and allows coincidences among these alternatives.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 149–162; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.fullSupport_iff

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_Choice_eval_allSkip
import Theorems.Thm_Couret_Choice_eval_of_not_omitted
import Theorems.Thm_Couret_Choice_eval_of_not_picked
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

theorem fullSupport_iff (M : CMonoid α) (w : Word α) (u : α) :
    fullSupport M w u ↔ properSupport M w u ∨ u = M.one ∨ u = total M w := by sorry


































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
