-- Prove2me | Theorems.Thm_Couret_semantic_step
-- name    : Couret.semantic_step
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:06.98813+00:00
-- url     : https://prove2.me/theorems/26726d8d-46e9-488d-aa56-8ea14f731824
-- title:
--   The semantic support state respects appending a factor
-- statement:
--   Let $M$ be a commutative monoid on a type $A$, $w$ a finite word over $A$, and $P(w)$ its total product. A selection chooses positions of $w$; a proper selection chooses at least one position and omits at least one. Define the semantic state of the empty word as initial, and that of a nonempty word as its total product together with its proper-selection support. The update sends initial input $g$ to total $g$ with empty proper support; on an active state $(r,U)$ it sends $g$ to $(rg,U\cup gU\cup\{r,g\})$. Then
--
--   $$\operatorname{step}(\operatorname{semantic}(w),g)=\operatorname{semantic}(wg).$$
--
--   This includes the empty-word boundary case.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 228–241; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.semantic_step

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_properSupport_snoc
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

theorem semantic_step (M : CMonoid α) (w : Word α) (g : α) :
    step M (semanticState M w) g = semanticState M (.snoc w g) := by sorry




















/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret
