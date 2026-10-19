-- Prove2me | Theorems.Thm_actuarial_d_deferred_guarantee_factor
-- name    : actuarial_d_deferred_guarantee_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:28:16.577074+00:00
-- url     : https://prove2.me/theorems/04eb4849-3a8e-423a-b522-33924be50079
-- title:
--   Deferred member guarantee decomposition
-- statement:
--   Deferred member guarantee decomposition. The guarantee pension consists of ordinary survivor payments and extra guaranteed-only instalments. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_G=a_x+a_U
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_deferGuaranteed
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferTopup

open ActuarialJointD

theorem actuarial_d_deferred_guarantee_factor (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : deferGuaranteed h a n g p d b = deferX h a n p d b + deferTopup h a n g p d b := by sorry
