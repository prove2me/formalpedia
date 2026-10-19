-- Prove2me | Theorems.Thm_actuarial_d_advanced_factor_reconciliation
-- name    : actuarial_d_advanced_factor_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:30:09.018329+00:00
-- url     : https://prove2.me/theorems/bccbf840-c068-425e-95f5-437eefa6237e
-- title:
--   Complex survivor contract via single/joint and guarantee corrections
-- statement:
--   Complex survivor contract via single/joint and guarantee corrections. Independent factor decomposition separates marginal annuities, the genuine joint discount factor, post-death guarantee and blocked reversion. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V=a_x+a_U+\rho(a_y-a_{xy}-a_O)+V_{\text{death riders}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_advancedValue
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferTopup
import Definitions.Def_actuarial_d_deferY
import Definitions.Def_actuarial_d_deferJoint
import Definitions.Def_actuarial_d_deferOverlap
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie

open ActuarialJointD

theorem actuarial_d_advanced_factor_reconciliation (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : advancedValue h a n g p d b rho f s fx fy ft = deferX h a n p d b + deferTopup h a n g p d b + rho * (deferY h a n p d b - deferJoint h a n p d b - deferOverlap h a n g p d b) + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d := by sorry
