-- Prove2me | Theorems.Thm_actuarial_f_bridge_adds_separate_instalment
-- name    : actuarial_f_bridge_adds_separate_instalment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:21:09.329801+00:00
-- url     : https://prove2.me/theorems/bf324999-6337-4cf3-8152-2b62071e1f65
-- title:
--   Bridge adds separate instalment
-- statement:
--   A scheme-specified temporary bridging pension is a separate additive cashflow on its own start and cessation dates.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{\text{bridge}}_t=C_t+B\mathbf1_{\{u\le t<v\}}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeAugmentedInstalment
import Definitions.Def_actuarial_f_bridgeInstalment
import Definitions.Def_actuarial_f_totalInstalment

open ActuarialUnderpinsF

theorem actuarial_f_bridge_adds_separate_instalment
    (h r g z i j t start stop : ℕ) (bridge : ℝ)
    (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) :
    bridgeAugmentedInstalment h r g z i j t start stop bridge
        a b c s estate g0 g1 gs ge =
      totalInstalment h r g z i j t a b c s estate g0 g1 gs ge +
        bridgeInstalment start stop t bridge := by sorry
