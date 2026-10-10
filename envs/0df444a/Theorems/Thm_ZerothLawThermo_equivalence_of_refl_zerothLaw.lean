-- Prove2me | Theorems.Thm_ZerothLawThermo_equivalence_of_refl_zerothLaw
-- name    : ZerothLawThermo.equivalence_of_refl_zerothLaw
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:24:54.117486+00:00
-- url     : https://prove2.me/theorems/6d65be3b-72a3-467e-b028-ea9fd0ce656d
-- title:
--   Reflexivity and the zeroth law make thermal equilibrium an equivalence relation
-- statement:
--   Let $S$ be a type of thermodynamic systems and $\mathrm{TE}$ a binary relation on $S$ ("is in thermal equilibrium with"). Assume
--
--   1. every system is in thermal equilibrium with itself: $\mathrm{TE}(A,A)$ for all $A\in S$;
--   2. the zeroth law: whenever $\mathrm{TE}(A,C)$ and $\mathrm{TE}(B,C)$, also $\mathrm{TE}(A,B)$.
--
--   Then $\mathrm{TE}$ is an equivalence relation on $S$, i.e. it is reflexive, symmetric and transitive.
--
--   This is the precise mathematical content of the zeroth law: thermal equilibrium is an equivalence relation, which is what allows it to be represented by equality of a temperature.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Section "Equivalence relation" (paragraphs following the right-Euclidean statement: "Binary relations that are both reflexive and Euclidean are equivalence relations. Thus, again implicitly assuming reflexivity, the zeroth law is therefore often expressed as a right-Euclidean statement"); also lead section: "It makes the relation of thermal equilibrium between systems an equivalence relation"

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem ZerothLawThermo.equivalence_of_refl_zerothLaw {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLaw TE) :
    Equivalence TE := by sorry
