-- Prove2me | Theorems.Thm_actuarial_c_path_scale
-- name    : actuarial_c_path_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:16:05.765276+00:00
-- url     : https://prove2.me/theorems/fabc8f75-f5e4-43e5-88fa-fdc2e0e2409f
-- title:
--   Claim PV respects monetary scaling
-- statement:
--   Claim PV respects monetary scaling.
--
--   Mathematical relation:
--
--   $$
--   Z_{cb}(k)=cZ_b(k)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, year-end death claim present value, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path

open ActuarialAssurances

theorem actuarial_c_path_scale (h k : ℕ) (v c : ℝ) (b : ℕ → ℝ) : path h v (fun j => c*b j) k=c*path h v b k := by sorry
