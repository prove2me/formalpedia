-- Prove2me | Theorems.Thm_actuarial_f_spouse_due_at_first_following_year
-- name    : actuarial_f_spouse_due_at_first_following_year
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:12:18.94821+00:00
-- url     : https://prove2.me/theorems/71001a2c-4336-4c99-835f-7fac05901ad0
-- title:
--   Spouse due at first following year
-- statement:
--   The first post-death annual date carries a survivor instalment when the survivor remains eligible.
--
--   The defining or asserted relationship is:
--
--   $$
--   i<H,\ i+1\le j\Longrightarrow s_{ij}(i+1)=1
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem actuarial_f_spouse_due_at_first_following_year (h i j : ℕ)
    (hi : i < h) (hj : i + 1 ≤ j) :
    spouseDue h i j (i + 1) = 1 := by sorry
