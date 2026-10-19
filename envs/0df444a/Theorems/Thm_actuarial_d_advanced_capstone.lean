-- Prove2me | Theorems.Thm_actuarial_d_advanced_capstone
-- name    : actuarial_d_advanced_capstone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:32:32.911392+00:00
-- url     : https://prove2.me/theorems/09532989-3c60-4d33-a963-3bd228572fab
-- title:
--   Integrated deferred joint-and-survivor pension with guarantee, death-order riders and two independent valuations
-- statement:
--   Integrated deferred joint-and-survivor pension with guarantee, death-order riders and two independent valuations. Under a coherent joint death-time law and a bounded payment horizon, the same realised guaranteed deferred member/spouse cashflow has occupation and independent factor values, reduces to the ordinary contract, and reconciles first/second-death claim partitions. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{occupation}}=a_G+\rho a_R+V_{\text{death riders}}=a_x+a_U+\rho(a_y-a_{xy}-a_O)+V_{\text{death riders}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_advancedValue
import Definitions.Def_actuarial_d_advancedPath
import Definitions.Def_actuarial_d_deferGuaranteed
import Definitions.Def_actuarial_d_deferBlockedRev
import Definitions.Def_actuarial_d_deferX
import Definitions.Def_actuarial_d_deferTopup
import Definitions.Def_actuarial_d_deferY
import Definitions.Def_actuarial_d_deferJoint
import Definitions.Def_actuarial_d_deferOverlap
import Definitions.Def_actuarial_d_totalValue
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie
import Definitions.Def_actuarial_d_assureXSecond
import Definitions.Def_actuarial_d_assureYSecond
import Definitions.Def_actuarial_d_valid

open ActuarialJointD

theorem actuarial_d_advanced_capstone (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) (hp : valid h p) (hterm : a + n ≤ h+1) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) : (advancedValue h a n g p d b rho f s fx fy ft = deferGuaranteed h a n g p d b + rho * deferBlockedRev h a n g p d b + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d) ∧ (advancedValue h a n g p d b rho f s fx fy ft = deferX h a n p d b + deferTopup h a n g p d b + rho * (deferY h a n p d b - deferJoint h a n p d b - deferOverlap h a n g p d b) + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d) ∧ (advancedValue h 0 n 0 p d b rho f s fx fy ft = totalValue h n p d b rho f s fx fy ft) ∧ (assureFirst h p d = assureXFirst h p d + assureYFirst h p d + assureTie h p d) ∧ (assureSecond h p d = assureXSecond h p d + assureYSecond h p d + assureTie h p d) := by sorry
