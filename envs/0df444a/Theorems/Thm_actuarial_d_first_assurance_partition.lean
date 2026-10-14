-- Prove2me | Theorems.Thm_actuarial_d_first_assurance_partition
-- name    : actuarial_d_first_assurance_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T07:02:50.624502+00:00
-- url     : https://prove2.me/theorems/2b62acbe-7554-4aa2-8af4-d3218d4ea3ff
-- title:
--   First-death assurance partition
-- statement:
--   First-death assurance partition. Strict first deaths and ties exhaust first-death claims without double counting. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A^{(1)}=A_{x\prec y}^{(1)}+A_{y\prec x}^{(1)}+A_{\text{tie}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8.1, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

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

theorem actuarial_d_first_assurance_partition (h : ℕ) (p : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : assureFirst h p d = assureXFirst h p d + assureYFirst h p d + assureTie h p d := by sorry
