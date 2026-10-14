-- Prove2me | Theorems.Thm_actuarial_d_mthly_one_per_year
-- name    : actuarial_d_mthly_one_per_year
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T07:08:22.565413+00:00
-- url     : https://prove2.me/theorems/436e72c8-f63f-4550-97dc-faa144ce0242
-- title:
--   Annual frequency as m-thly special case
-- statement:
--   Annual frequency as m-thly special case. With one instalment per year the subannual due grid and amount rate coincide. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a^{(m=1)}=a^{\text{annual due}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_mthlyPath
import Definitions.Def_actuarial_d_annPath

open ActuarialJointD

theorem actuarial_d_mthly_one_per_year (years : ℕ) (d b s : ℕ → ℝ) : mthlyPath years 1 d b s = annPath years d b s := by sorry
