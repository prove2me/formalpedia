-- Prove2me | Theorems.Thm_actuarial_e_expect_constant
-- name    : actuarial_e_expect_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:52:41.963279+00:00
-- url     : https://prove2.me/theorems/630e9430-b2aa-4c17-b756-d350f43897f3
-- title:
--   Normalisation of a deterministic payment
-- statement:
--   Normalisation of a deterministic payment. A certain benefit has expected amount equal to its promised amount under a normalised joint law. All event-year endpoints follow the contract's strict and weak inequalities. Rates and cash amounts are parameterised; this remains an open formal theorem.
--
--   The contractual and mortality relation is:
--
--   $$
--   \sum_{i,j}p_{ij}=1\quad\Rightarrow\quad\mathbb{E}_p[k]=k
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
import Definitions.Def_actuarial_e_validLaw
import Definitions.Def_actuarial_e_expect

open ActuarialDeathE

theorem actuarial_e_expect_constant (h : ℕ) (p : ℕ → ℕ → ℝ) (k : ℝ) (hp : validLaw h p) : expect h p (fun i j => k) = k := by sorry
