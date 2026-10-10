-- Prove2me | Theorems.Thm_ZerothLawThermo_existence_of_temperature
-- name    : ZerothLawThermo.existence_of_temperature
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:42.436108+00:00
-- url     : https://prove2.me/theorems/26524481-6a9b-403c-80ff-9935c0b8c649
-- title:
--   Zeroth law of thermodynamics: existence of an empirical temperature
-- statement:
--   This is the "existence of temperature" form of the zeroth law of thermodynamics.
--
--   Let $S$ be a type of thermodynamic systems and $\mathrm{TE}$ the relation of thermal equilibrium on $S$. Assume
--
--   1. every system is in thermal equilibrium with itself: $\mathrm{TE}(A,A)$ for all $A\in S$;
--   2. the zeroth law: if two systems are both in thermal equilibrium with a third system, they are in thermal equilibrium with each other, i.e. $\mathrm{TE}(A,C)\wedge\mathrm{TE}(B,C)\Rightarrow\mathrm{TE}(A,B)$.
--
--   Then there exist a set of labels $T$ and a single-valued function $t:S\to T$ (an empirical temperature) such that
--   $$\forall A,B\in S,\qquad \mathrm{TE}(A,B)\iff t(A)=t(B).$$
--
--   In words, the condition for thermal equilibrium between systems is equality of a temperature. This is the logical foundation for thermometry and for empirical temperature scales.
--
--   **Formalization Note** The label type $T$ is arbitrary (it lives in the same universe as $S$); order and continuity properties of real temperature scales are not part of the zeroth law and are not asserted.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Lead section ("A quantity that is the same for two systems, if they can be placed in thermal equilibrium with each other, is a scale of temperature. The zeroth law is needed for the definition of such scales"); section "Equivalence relation"; section "History", Fowler & Guggenheim (ref. 17): "If two assemblies are each in thermal equilibrium with a third assembly, they are in thermal equilibrium with each other ... it may be shown to follow that the condition for thermal equilibrium between several assemblies is the equality of a certain single-valued function of the thermodynamic states of the assemblies, which may be called the temperature t"

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

universe u

open ZerothLawThermo

theorem ZerothLawThermo.existence_of_temperature {S : Type u} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLaw TE) :
    ∃ (T : Type u) (t : S → T), IsEmpiricalTemperature TE t := by sorry
