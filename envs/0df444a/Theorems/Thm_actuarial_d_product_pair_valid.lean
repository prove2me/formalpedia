-- Prove2me | Theorems.Thm_actuarial_d_product_pair_valid
-- name    : actuarial_d_product_pair_valid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:04:05.521602+00:00
-- url     : https://prove2.me/theorems/f1a354a7-fcb9-4ba2-b455-8ecce9cdebaf
-- title:
--   Coherent independent two-life law
-- statement:
--   Coherent independent two-life law. Four equally probable death-year pairs define a normalised independent joint law. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{ij}=\tfrac14\quad(i,j\in\{0,1\})
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_productPairLaw

open ActuarialJointD

theorem actuarial_d_product_pair_valid  : valid 1 productPairLaw := by sorry
