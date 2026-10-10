-- Prove2me | Theorems.Thm_ZerothLawThermo_zerothLaw_iff_zerothLawPlanck_of_refl
-- name    : ZerothLawThermo.zerothLaw_iff_zerothLawPlanck_of_refl
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:26:29.52331+00:00
-- url     : https://prove2.me/theorems/f7ede297-5e84-49a9-97fe-5afceb06b544
-- title:
--   Under reflexivity, the two Euclidean forms of the zeroth law are equivalent
-- statement:
--   Let $S$ be a type of thermodynamic systems and $\mathrm{TE}$ a binary relation on $S$ such that $\mathrm{TE}(A,A)$ for all $A\in S$. Then the following are equivalent:
--
--   1. the zeroth law (right-Euclidean form): $\mathrm{TE}(A,C)\wedge\mathrm{TE}(B,C)\Rightarrow\mathrm{TE}(A,B)$ for all $A,B,C$;
--   2. Planck's form (left-Euclidean form): $\mathrm{TE}(C,A)\wedge\mathrm{TE}(C,B)\Rightarrow\mathrm{TE}(A,B)$ for all $A,B,C$.
--
--   This justifies the source's passage from Planck's statement to the now-standard statement of the law, once reflexivity is assumed.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Section "Equivalence relation": Planck's left-Euclidean statement, then "Thus, again implicitly assuming reflexivity, the zeroth law is therefore often expressed as a right-Euclidean statement: If two systems are in thermal equilibrium with a third system, then they are in thermal equilibrium with each other."

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem ZerothLawThermo.zerothLaw_iff_zerothLawPlanck_of_refl {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) :
    ZerothLaw TE ↔ ZerothLawPlanck TE := by sorry
