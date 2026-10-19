-- Prove2me | Theorems.Thm_actuarial_d_capstone
-- name    : actuarial_d_capstone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:32:09.05335+00:00
-- url     : https://prove2.me/theorems/afef1308-4947-4ef6-8767-64f321846226
-- title:
--   Two-route joint-and-survivor valuation with order-sensitive death assurances
-- statement:
--   Two-route joint-and-survivor valuation with order-sensitive death assurances. The realised cashflow expectation is reconciled with both single/joint/reversionary factor systems, and the first- and second-death riders are reconciled against their disjoint strict-order and tied-death events. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{occupation}}=a_x+\rho a_{y\mid x}+V_{\text{death riders}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_totalValue
import Definitions.Def_actuarial_d_totalPath
import Definitions.Def_actuarial_d_annX
import Definitions.Def_actuarial_d_annRev
import Definitions.Def_actuarial_d_annLast
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie
import Definitions.Def_actuarial_d_assureXSecond
import Definitions.Def_actuarial_d_assureYSecond

open ActuarialJointD

theorem actuarial_d_capstone (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : totalValue h n p d b rho f s fx fy ft = annX h n p d b + rho * annRev h n p d b + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d ∧ totalValue h n p d b rho f s fx fy ft = (1-rho) * annX h n p d b + rho * annLast h n p d b + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d ∧ assureFirst h p d = assureXFirst h p d + assureYFirst h p d + assureTie h p d ∧ assureSecond h p d = assureXSecond h p d + assureYSecond h p d + assureTie h p d := by sorry
