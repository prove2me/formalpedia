-- Prove2me | Theorems.Thm_ZerothLawThermo_symm_of_refl_zerothLaw
-- name    : ZerothLawThermo.symm_of_refl_zerothLaw
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:09.158422+00:00
-- url     : https://prove2.me/theorems/b3d11956-598c-471e-875f-ed9076f123a5
-- title:
--   Thermal equilibrium is symmetric
-- statement:
--   Let $S$ be a type of thermodynamic systems and $\mathrm{TE}$ a binary relation on $S$ such that $\mathrm{TE}(A,A)$ for all $A$, and satisfying the zeroth law ($\mathrm{TE}(A,C)\wedge\mathrm{TE}(B,C)\Rightarrow\mathrm{TE}(A,B)$). Then for all systems $A,B$,
--   $$\mathrm{TE}(A,B)\ \Longrightarrow\ \mathrm{TE}(B,A).$$
--
--   So thermal equilibrium is a mutual relation between two systems.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Section "Equivalence relation": "One consequence of an equivalence relationship is that the equilibrium relationship is symmetric: If A is in thermal equilibrium with B, then B is in thermal equilibrium with A."

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem ZerothLawThermo.symm_of_refl_zerothLaw {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLaw TE) (A B : S) (hAB : TE A B) :
    TE B A := by sorry
