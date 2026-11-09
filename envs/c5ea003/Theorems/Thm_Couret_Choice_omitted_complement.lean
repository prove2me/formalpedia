-- Prove2me | Theorems.Thm_Couret_Choice_omitted_complement
-- name    : Couret.Choice.omitted_complement
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:24:52.699889+00:00
-- url     : https://prove2.me/theorems/bffba4e9-2b19-4524-bb48-e771e7985806
-- title:
--   Complement exchanges selection and omission
-- statement:
--   Let $w$ be a finite word over any type and let $s$ select some of its positions. Then
--
--   $$s^{\mathrm c}\text{ omits a position}\iff s\text{ selects a position}.$$
--
--   Both sides are false for the empty word.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 116–121; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.Choice.omitted_complement

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

theorem omitted_complement {w : Word α} (s : Choice w) :
    omitted (complement s) ↔ picked s := by sorry




end Choice







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
