-- Prove2me | Theorems.Thm_actuarial_e_guarantee_option_capital
-- name    : actuarial_e_guarantee_option_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-18T20:45:24.583951+00:00
-- url     : https://prove2.me/theorems/7dbf30dd-2f4e-4fbd-963b-c6e7bee5e883
-- title:
--   Commuted estate guarantee uses the single capital payment
-- statement:
--   Commuted estate guarantee uses the single capital payment. The same contractual switch suppresses continuation instalments when the GBP lump sum is selected. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   \kappa=1\Rightarrow G_{\text{option}}=G_{\text{capital}}
--   $$
--
--   This is an open theorem statement; no formal proof is claimed. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 10, p. 388, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_guaranteeCapitalPV
import Definitions.Def_actuarial_e_guaranteeOptionPV

open ActuarialDeathE

theorem actuarial_e_guarantee_option_capital (n h r g i : ℕ) (disc : ℕ → ℝ) (forward : ℕ → ℕ → ℝ) (base : ℕ → ℝ) : guaranteeOptionPV n h r g i disc forward base true = guaranteeCapitalPV n h r g i disc forward base := by sorry
