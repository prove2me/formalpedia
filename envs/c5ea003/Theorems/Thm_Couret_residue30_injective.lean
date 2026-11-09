-- Prove2me | Theorems.Thm_Couret_residue30_injective
-- name    : Couret.residue30_injective
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:51:40.501247+00:00
-- url     : https://prove2.me/theorems/28d82b94-cf08-48e9-924d-02ab8f253b4a
-- title:
--   The eight residue representatives determine their codes
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. For all $a,b\in C$,
--
--   $$\rho(a)=\rho(b)\Longrightarrow a=b.$$
--
--   Thus the chosen unit representatives have no collisions.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 369–370; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.residue30_injective

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

theorem residue30_injective : ∀ a b : Code30,
    residue30 a = residue30 b → a = b := by sorry








end Couret
