-- Prove2me | Theorems.Thm_actuarial_d_perfect_pair_valid
-- name    : actuarial_d_perfect_pair_valid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:03:50.128979+00:00
-- url     : https://prove2.me/theorems/35a0490a-e448-47d7-8edb-6c2b37cfa6d2
-- title:
--   Coherent perfectly dependent law
-- statement:
--   Coherent perfectly dependent law. Two diagonal cells of probability one half each define a valid dependent joint death-year distribution. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{00}=p_{11}=\tfrac12,\quad p_{01}=p_{10}=0
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_perfectPairLaw

open ActuarialJointD

theorem actuarial_d_perfect_pair_valid  : valid 1 perfectPairLaw := by sorry
