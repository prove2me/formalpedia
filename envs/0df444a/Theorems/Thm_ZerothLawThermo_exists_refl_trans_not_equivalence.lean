-- Prove2me | Theorems.Thm_ZerothLawThermo_exists_refl_trans_not_equivalence
-- name    : ZerothLawThermo.exists_refl_trans_not_equivalence
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:08.796418+00:00
-- url     : https://prove2.me/theorems/cd0e6a8e-2f54-4a0d-97d2-9e79f2c13cd3
-- title:
--   A reflexive, transitive relation need not be an equivalence relation
-- statement:
--   There exist a type $S$ and a binary relation $R$ on $S$ such that
--
--   1. $R$ is reflexive: $R(A,A)$ for all $A\in S$;
--   2. $R$ is transitive: $R(A,B)\wedge R(B,C)\Rightarrow R(A,C)$;
--   3. $R$ is **not** an equivalence relation.
--
--   Thus the transitive formulation of the zeroth law, together with reflexivity, does not by itself make thermal equilibrium an equivalence relation; symmetry must be assumed separately.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Section "Equivalence relation": "A reflexive, transitive relation does not guarantee an equivalence relationship. For the above statement to be true, both reflexivity and symmetry must be implicitly assumed."

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem ZerothLawThermo.exists_refl_trans_not_equivalence :
    ∃ (S : Type) (R : S → S → Prop),
      (∀ A : S, R A A) ∧ (∀ A B C : S, R A B → R B C → R A C) ∧ ¬ Equivalence R := by sorry
