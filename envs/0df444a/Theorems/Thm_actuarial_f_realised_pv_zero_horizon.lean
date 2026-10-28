-- Prove2me | Theorems.Thm_actuarial_f_realised_pv_zero_horizon
-- name    : actuarial_f_realised_pv_zero_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:18:22.926862+00:00
-- url     : https://prove2.me/theorems/5bd92325-a52e-4c20-9d6c-ef157e27280a
-- title:
--   Realised pv zero horizon
-- statement:
--   With retirement after date zero, the zero-horizon model has no member, spouse or estate pension payments.
--
--   The defining or asserted relationship is:
--
--   $$
--   H=0,\ r>0\Longrightarrow V_{zij}=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_realisedPV

open ActuarialUnderpinsF

theorem actuarial_f_realised_pv_zero_horizon (r g z i j : ℕ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) (hr : 0 < r) :
    realisedPV 0 r g z i j disc a b c s estate g0 g1 gs ge = 0 := by sorry
