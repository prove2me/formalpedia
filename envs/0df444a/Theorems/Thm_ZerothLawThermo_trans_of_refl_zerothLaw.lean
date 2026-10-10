-- Prove2me | Theorems.Thm_ZerothLawThermo_trans_of_refl_zerothLaw
-- name    : ZerothLawThermo.trans_of_refl_zerothLaw
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:27:45.630552+00:00
-- url     : https://prove2.me/theorems/41ddf758-9d90-4307-a1ba-4088c5283856
-- title:
--   Thermal equilibrium is transitive
-- statement:
--   Let $S$ be a type of thermodynamic systems and $\mathrm{TE}$ a binary relation on $S$ such that $\mathrm{TE}(A,A)$ for all $A$, and satisfying the zeroth law ($\mathrm{TE}(A,C)\wedge\mathrm{TE}(B,C)\Rightarrow\mathrm{TE}(A,B)$). Then for all systems $A,B,C$,
--   $$\mathrm{TE}(A,B)\ \wedge\ \mathrm{TE}(B,C)\ \Longrightarrow\ \mathrm{TE}(A,C).$$
--
--   This is the form of the law most often quoted in introductory texts.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; Section "Equivalence relation": "Another consequence of equivalence is that thermal equilibrium is described as a transitive relation: If A is in thermal equilibrium with B and if B is in thermal equilibrium with C, then A is in thermal equilibrium with C."

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem ZerothLawThermo.trans_of_refl_zerothLaw {S : Type*} (TE : S → S → Prop)
    (hrefl : ∀ A : S, TE A A) (hzero : ZerothLaw TE) (A B C : S)
    (hAB : TE A B) (hBC : TE B C) :
    TE A C := by sorry
