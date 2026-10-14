-- Prove2me | Theorems.Thm_actuarial_c_cont_fractional_grid_maturity
-- name    : actuarial_c_cont_fractional_grid_maturity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:35:57.143982+00:00
-- url     : https://prove2.me/theorems/dbe9d663-9af7-4d42-933d-24b732723be5
-- title:
--   M-thly payment grid reaches contractual maturity
-- statement:
--   After m times n payment intervals, the m-thly grid coincides with contractual maturity n.
--
--   This is an open proof obligation under the precise quantifiers and assumptions of its Lean statement. Numerical falsification tests and declaration checks do not establish a formal proof.
-- source:
--   Original derived actuarial result informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 7; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/c07.xhtml; and Dickson–Hardy–Waters (2020), DOI 10.1017/9781108784184. Not a verbatim textbook theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_fractionalTime

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_fractional_grid_maturity (m n : ℕ) (hm : 0 < m) :
    fractionalTime m (m*n) = (n : ℝ) := by sorry
