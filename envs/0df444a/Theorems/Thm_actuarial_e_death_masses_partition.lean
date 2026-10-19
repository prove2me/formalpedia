-- Prove2me | Theorems.Thm_actuarial_e_death_masses_partition
-- name    : actuarial_e_death_masses_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T18:28:10.427053+00:00
-- url     : https://prove2.me/theorems/2ff895a3-46b9-4d69-8b7e-db0860184835
-- title:
--   Death-state event probabilities add without multiple claims
-- statement:
--   Death-state event probabilities add without multiple claims. The probabilities of mutually exclusive active, deferred and retired deaths exhaust exactly the observed member-death mass. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   \Pr(A)+\Pr(D)+\Pr(R)=\Pr(i<h)
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 9, p. 359, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_expect
import Definitions.Def_actuarial_e_activeDeathMass
import Definitions.Def_actuarial_e_deferredDeathMass
import Definitions.Def_actuarial_e_retiredDeathMass

open ActuarialDeathE

theorem actuarial_e_death_masses_partition (h e r : ℕ) (p : ℕ → ℕ → ℝ) (he : e ≤ r) : activeDeathMass h e p + deferredDeathMass h e r p + retiredDeathMass h r p = expect h p (fun i j => if i < h then (1 : ℝ) else 0) := by sorry
