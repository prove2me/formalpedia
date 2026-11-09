-- Prove2me | Theorems.Thm_Couret_mul30_residue
-- name    : Couret.mul30_residue
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:08.660882+00:00
-- url     : https://prove2.me/theorems/907ab0d9-c8ca-4b78-889a-9acbc56588b8
-- title:
--   The residue code respects multiplication modulo 30
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. For every $a,b\in C$, with code multiplication given by coordinatewise addition,
--
--   $$\rho(ab)=(\rho(a)\rho(b))\bmod30.$$
--
--   This makes the coordinate code compatible with unit multiplication.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 366–367; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.mul30_residue

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

theorem mul30_residue : ∀ a b : Code30,
    residue30 (mul30 a b) = (residue30 a * residue30 b) % 30 := by sorry










end Couret
