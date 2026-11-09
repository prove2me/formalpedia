-- Prove2me | Theorems.Thm_Couret_properSupport_is_nontrivial_divisor
-- name    : Couret.properSupport_is_nontrivial_divisor
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:13.521789+00:00
-- url     : https://prove2.me/theorems/81efae27-cf1e-4ab6-8314-bb6b3ac87e1e
-- title:
--   Proper selections of factors above one give proper divisors
-- statement:
--   Let $w$ be a word whose entries are all at least two and let $N$ be its product. If a nonempty proper selection has product $d$, then $$d\mid N,\qquad1<d<N.$$
--
--   The stated entry condition is the word predicate, not a lower bound on the word length.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 302–317; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.properSupport_is_nontrivial_divisor

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_Choice_eval_mul_complement
import Theorems.Thm_Couret_Choice_picked_complement
import Theorems.Thm_Couret_pickedProduct_gt_one
import Theorems.Thm_Couret_selectedProduct_dvd_total
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

theorem properSupport_is_nontrivial_divisor (w : Word Nat) (hw : w.atLeastTwo)
    (d : Nat) (h : properSupport natProduct w d) :
    d ∣ total natProduct w ∧ 1 < d ∧ d < total natProduct w := by sorry


/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
