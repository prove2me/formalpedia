-- Prove2me | Theorems.Thm_actuarial_f_guarantee_first_window
-- name    : actuarial_f_guarantee_first_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:13:57.809215+00:00
-- url     : https://prove2.me/theorems/1c610bcd-7a19-4d99-9516-d5da7b9ef3a7
-- title:
--   Guarantee first window
-- statement:
--   Every instalment within the permitted post-death, pre-expiry estate guarantee window is due.
--
--   The defining or asserted relationship is:
--
--   $$
--   r\le i<H,\ i<t<r+g\Longrightarrow e_i(t)=1
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue

open ActuarialUnderpinsF

theorem actuarial_f_guarantee_first_window (h r g i t : ℕ)
    (hr : r ≤ i) (hc : i < h) (hi : i < t) (hd : r ≤ t)
    (hg : t < r + g) : estateDue h r g i t = 1 := by sorry
