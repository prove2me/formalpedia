-- Prove2me | Theorems.Thm_actuarial_f_total_instalment_reconciles
-- name    : actuarial_f_total_instalment_reconciles
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:18:06.986081+00:00
-- url     : https://prove2.me/theorems/a46d806a-78f4-4e90-9bc0-8463701c454a
-- title:
--   Total instalment reconciles
-- statement:
--   The complete due benefit can be assembled from the two separately indexed member tranches and the distinct survivor and estate states.
--
--   The defining or asserted relationship is:
--
--   $$
--   C_t=(U_zG^{(1)}_t+C_zG^{(2)}_t)m_i(t)+C^S_t+C^E_t
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_totalInstalment

open ActuarialUnderpinsF

theorem actuarial_f_total_instalment_reconciles (h r g z i j t : ℕ)
    (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    totalInstalment h r g z i j t a b c s estate g0 g1 gs ge =
      (awardBase a b z * g0 t + c z * g1 t) * memberDue r i t +
      spouseInstalment h z i j t s gs + estateInstalment h r g z i t estate ge := by sorry
