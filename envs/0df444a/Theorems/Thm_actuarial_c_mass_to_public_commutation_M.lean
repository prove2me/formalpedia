-- Prove2me | Theorems.Thm_actuarial_c_mass_to_public_commutation_M
-- name    : actuarial_c_mass_to_public_commutation_M
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:32:12.197413+00:00
-- url     : https://prove2.me/theorems/fa98c5dc-c25f-4e4c-b300-437377fc5836
-- title:
--   The event-derived level assurance equals the public discounted death commutation sum after a derived cohort mapping
-- statement:
--   The event-derived level assurance equals the public discounted death commutation sum after a derived cohort mapping.
--
--   Mathematical relation:
--
--   $$
--   A_h=M_0(S,v,h)
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.7, general identity and actuarial notation, printed p. 71. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem. Reuses public actuarial_faM (Prove2Me theorem UUID a7b064c7-41fc-4f04-9b9a-ac23da3a15c7) under the same Mathlib revision.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_massPV
import Definitions.Def_actuarial_c_massCohort
import Definitions.Def_actuarial_faM

open ActuarialAssurances

theorem actuarial_c_mass_to_public_commutation_M (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : massPV h v (fun _ => 1) p=ActuarialFoundations.faM (massCohort h p) v h 0 := by sorry
