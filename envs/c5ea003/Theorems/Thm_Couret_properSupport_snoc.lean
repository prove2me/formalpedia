-- Prove2me | Theorems.Thm_Couret_properSupport_snoc
-- name    : Couret.properSupport_snoc
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:47:31.59026+00:00
-- url     : https://prove2.me/theorems/71c7a332-401e-4ae1-baa6-18955f738a09
-- title:
--   Appending a monoid element updates proper products
-- statement:
--   Let $M$ be a commutative monoid on a type $\alpha$, $w$ a nonempty word, and $g,u\in\alpha$. Then $$u\in P_M(wg)\iff u\in P_M(w)\ \lor\ \exists v\in P_M(w),\ gv=u\ \lor\ u=\operatorname{total}_M(w)\ \lor\ u=g.$$
--
--   Here $P_M$ uses nonempty proper choices of positions, so repeated entries are allowed.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 177–213; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.properSupport_snoc

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

theorem properSupport_snoc (M : CMonoid α) (w : Word α) (hw : w.nonempty)
    (g u : α) :
    properSupport M (.snoc w g) u ↔
      properSupport M w u ∨
      (∃ v, properSupport M w v ∧ M.mul g v = u) ∨
      u = total M w ∨ u = g := by sorry




























/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
