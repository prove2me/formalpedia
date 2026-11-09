-- Prove2me | Theorems.Thm_Couret_run_correct
-- name    : Couret.run_correct
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:30.475213+00:00
-- url     : https://prove2.me/theorems/781fdfd5-2d3b-4b87-a9b6-2102e1cead0a
-- title:
--   The automaton run equals its word semantics
-- statement:
--   For any commutative monoid $M$ on a type $\alpha$ and every finite word $w$, $$\operatorname{run}_M(w)=\operatorname{semanticState}_M(w).$$
--
--   The identity includes the empty word and compares complete states.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 247–254; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.run_correct

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_semantic_step
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

theorem run_correct (M : CMonoid α) (w : Word α) :
    run M w = semanticState M w := by sorry
















/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
