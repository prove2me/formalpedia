-- Prove2me | Theorems.Thm_Couret_mod30_properSupport_snoc
-- name    : Couret.mod30_properSupport_snoc
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:00.275198+00:00
-- url     : https://prove2.me/theorems/e0387b0d-c51b-4ffb-a7e8-e034f9adfa40
-- title:
--   Appending a residue updates proper subproducts
-- statement:
--   For a nonempty word $w$ of residue codes and codes $g,u$, $$u\in P(wg)\iff u\in P(w)\ \lor\ \exists v\in P(w),\ gv=u\ \lor\ u=\operatorname{total}(w)\ \lor\ u=g,$$ where $P$ is the set of products of nonempty proper selections and multiplication is modulo 30. The nonempty-word hypothesis is explicit.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean, lines 380–386; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3; theorem Couret.mod30_properSupport_snoc

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







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/

theorem mod30_properSupport_snoc (w : Word Code30) (hw : w.nonempty)
    (g u : Code30) :
    properSupport mod30Product (.snoc w g) u ↔
      properSupport mod30Product w u ∨
      (∃ v, properSupport mod30Product w v ∧ mul30 g v = u) ∨
      u = total mod30Product w ∨ u = g := by sorry


end Couret
