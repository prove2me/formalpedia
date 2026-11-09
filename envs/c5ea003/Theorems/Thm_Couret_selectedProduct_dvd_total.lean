-- Prove2me | Theorems.Thm_Couret_selectedProduct_dvd_total
-- name    : Couret.selectedProduct_dvd_total
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:47:27.099191+00:00
-- url     : https://prove2.me/theorems/f64da0cf-a45b-4c9f-a041-a3b150e9224a
-- title:
--   Every selected natural product divides the total
-- statement:
--   Let $w$ be any finite word of natural numbers and $s$ any selection of its labeled occurrences. Then
--
--   $$\prod s\mid\prod w.$$
--
--   This includes empty words, empty selections, and zero factors.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 264–267; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.selectedProduct_dvd_total

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

theorem selectedProduct_dvd_total {w : Word Nat} (s : Choice w) :
    Choice.eval natProduct s ∣ total natProduct w := by sorry












/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
