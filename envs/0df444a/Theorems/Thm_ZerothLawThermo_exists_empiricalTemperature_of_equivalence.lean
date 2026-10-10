-- Prove2me | Theorems.Thm_ZerothLawThermo_exists_empiricalTemperature_of_equivalence
-- name    : ZerothLawThermo.exists_empiricalTemperature_of_equivalence
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:08.528559+00:00
-- url     : https://prove2.me/theorems/221f49b3-8720-48be-9c9b-8d85dba29116
-- title:
--   An equivalence relation of thermal equilibrium admits an empirical temperature tagging
-- statement:
--   Let $S$ be a type of thermodynamic systems and suppose thermal equilibrium $\mathrm{TE}$ is an equivalence relation on $S$. Then there exist a set of labels $T$ and a labelling $t:S\to T$ which is an empirical temperature for $\mathrm{TE}$:
--   $$\forall A,B\in S,\qquad \mathrm{TE}(A,B)\iff t(A)=t(B).$$
--
--   Two systems carry the same tag exactly when they are in thermal equilibrium; the set of labels is arbitrary.
--
--   **Formalization Note** The label type $T$ is required to live in the same universe as $S$.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Section "Equivalence relation": "This means that a unique \"tag\" can be assigned to every system, and if the \"tags\" of two systems are the same, they are in thermal equilibrium with each other, and if different, they are not." Also section "Foundation of temperature": "This partitioning allows any member of the subset to be uniquely \"tagged\" with a label identifying the subset to which it belongs. Although the labeling may be quite arbitrary, temperature is just such a labeling process".

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

universe u

open ZerothLawThermo

theorem ZerothLawThermo.exists_empiricalTemperature_of_equivalence {S : Type u} (TE : S → S → Prop)
    (hTE : Equivalence TE) :
    ∃ (T : Type u) (t : S → T), IsEmpiricalTemperature TE t := by sorry
