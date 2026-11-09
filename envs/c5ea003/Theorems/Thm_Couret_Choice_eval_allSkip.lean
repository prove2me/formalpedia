-- Prove2me | Theorems.Thm_Couret_Choice_eval_allSkip
-- name    : Couret.Choice.eval_allSkip
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:31.03994+00:00
-- url     : https://prove2.me/theorems/399b7218-2bed-440c-98d0-84bf2327abb9
-- title:
--   Skipping every occurrence yields the identity
-- statement:
--   Let $M$ be a commutative monoid on a type $\alpha$ and $w$ a finite word in $\alpha$. Selecting no labeled occurrences gives
--
--   $$\operatorname{eval}_M(\operatorname{allSkip}(w))=1_M.$$
--
--   This gives the empty-selection product for every word, including the empty word.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 65–69; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.Choice.eval_allSkip

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

theorem eval_allSkip (M : CMonoid α) (w : Word α) :
    eval M (allSkip w) = M.one := by sorry






















end Choice







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
