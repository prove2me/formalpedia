-- Prove2me | Theorems.Thm_actuarial_d_second_assurance_partition
-- name    : actuarial_d_second_assurance_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:03:02.648215+00:00
-- url     : https://prove2.me/theorems/36aae19d-2f77-4c5a-8a48-e361d7bf216c
-- title:
--   Second-death assurance partition
-- statement:
--   Second-death assurance partition. Strict later-death claims and tied deaths exhaust observed second-death claims. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A^{(2)}=A_{x\succ y}^{(2)}+A_{y\succ x}^{(2)}+A_{\text{tie}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.2, p. 154. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie
import Definitions.Def_actuarial_d_assureXSecond
import Definitions.Def_actuarial_d_assureYSecond

open ActuarialJointD

theorem actuarial_d_second_assurance_partition (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : assureSecond h p d = assureXSecond h p d + assureYSecond h p d + assureTie h p d := by sorry
