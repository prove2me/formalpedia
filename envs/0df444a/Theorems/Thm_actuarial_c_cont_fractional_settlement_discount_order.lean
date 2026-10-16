-- Prove2me | Theorems.Thm_actuarial_c_cont_fractional_settlement_discount_order
-- name    : actuarial_c_cont_fractional_settlement_discount_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:37:14.539872+00:00
-- url     : https://prove2.me/theorems/29b64f05-35b5-4d86-bc83-3dd8067a4061
-- title:
--   Discount ordering of immediate, fractional and annual death settlements
-- statement:
--   At nonnegative force of interest, actual-death payment dominates end-of-subperiod payment, which in turn dominates end-of-policy-year payment.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_cont_annualSettlementPV
import Definitions.Def_actuarial_c_cont_fractionalSettlementPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_fractional_settlement_discount_order (m h : ℕ) (delta t : ℝ)
    (hm : 0 < m) (hdelta : 0 ≤ delta)
    (ht : 0 ≤ t) (horizon : t < (h : ℝ)) :
    annualSettlementPV h delta t ≤ fractionalSettlementPV m h delta t ∧
      fractionalSettlementPV m h delta t ≤ deathPV (h : ℝ) delta t := by sorry
