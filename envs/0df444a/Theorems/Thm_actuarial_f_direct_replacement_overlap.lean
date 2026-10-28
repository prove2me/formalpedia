-- Prove2me | Theorems.Thm_actuarial_f_direct_replacement_overlap
-- name    : actuarial_f_direct_replacement_overlap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:20:54.812563+00:00
-- url     : https://prove2.me/theorems/06d6292b-58c1-4e0b-a3b4-fe17a1c9a5af
-- title:
--   Direct replacement overlap
-- statement:
--   The joint expected cashflow liability under parallel payment rules equals the replacement liability plus a separately priced survivor-guarantee overlap.
--
--   The defining or asserted relationship is:
--
--   $$
--   V_{\text{direct}}=V_{\text{rep}}+O
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_directEPV
import Definitions.Def_actuarial_f_guaranteeOverlapEPV
import Definitions.Def_actuarial_f_replacementEPV

open ActuarialUnderpinsF

theorem actuarial_f_direct_replacement_overlap
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ)
    (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    directEPV n h r g p disc a b c s estate g0 g1 gs ge =
      replacementEPV n h r g p disc a b c s estate g0 g1 gs ge +
      guaranteeOverlapEPV n h r g p disc s gs := by sorry
