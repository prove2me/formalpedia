-- Prove2me | Theorems.Thm_ZerothLawThermo_equivalence_of_refl_zerothLawPlanck
-- name    : ZerothLawThermo.equivalence_of_refl_zerothLawPlanck
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:42.346356+00:00
-- url     : https://prove2.me/theorems/83da3446-cd61-4fe1-9db1-b7b8d2cc7896
-- title:
--   Reflexivity and Planck's form of the zeroth law give an equivalence relation
-- statement:
--   Let $S$ be a type of thermodynamic systems and $\mathrm{TE}$ a binary relation on $S$. Assume
--
--   1. $\mathrm{TE}(A,A)$ for all $A\in S$;
--   2. Planck's form of the zeroth law: if a body $C$ is in thermal equilibrium with two bodies $A$ and $B$, i.e. $\mathrm{TE}(C,A)$ and $\mathrm{TE}(C,B)$, then $\mathrm{TE}(A,B)$.
--
--   Then $\mathrm{TE}$ is an equivalence relation on $S$.
--
--   This shows that Planck's (left-Euclidean) formulation of the law serves the same purpose as the usual one.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Section "Equivalence relation": Planck's statement "If a body C, be in thermal equilibrium with two other bodies, A and B, then A and B are in thermal equilibrium with one another" (ref. 8), followed by "This statement asserts that thermal equilibrium is a left-Euclidean relation ... If we also define that every thermodynamic system is in thermal equilibrium with itself, then thermal equilibrium is also a reflexive relation. Binary relations that are both reflexive and Euclidean are equivalence relations."

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem ZerothLawThermo.equivalence_of_refl_zerothLawPlanck {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLawPlanck TE) :
    Equivalence TE := by sorry
