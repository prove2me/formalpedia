-- Prove2me | Theorems.Thm_actuarial_d_tie_swap
-- name    : actuarial_d_tie_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:58:51.982565+00:00
-- url     : https://prove2.me/theorems/2082eab7-a11f-4b1b-bacb-45551e32f0e7
-- title:
--   Tie settlement symmetry
-- statement:
--   Tie settlement symmetry. Equal-tick deaths form a symmetric event with their own payment. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   C_{\text{tie}}(i,j)=C_{\text{tie}}(j,i)
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.8, p. 153. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_firstPath
import Definitions.Def_actuarial_d_secondPath
import Definitions.Def_actuarial_d_xFirstPath
import Definitions.Def_actuarial_d_yFirstPath
import Definitions.Def_actuarial_d_xSecondPath
import Definitions.Def_actuarial_d_ySecondPath
import Definitions.Def_actuarial_d_tiePath

open ActuarialJointD

theorem actuarial_d_tie_swap (h i j : ℕ) (d : ℕ → ℝ) : tiePath h d i j = tiePath h d j i := by sorry
