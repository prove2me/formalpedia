-- Prove2me | Theorems.Thm_actuarial_c_pure_reconcile
-- name    : actuarial_c_pure_reconcile
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:19:58.936789+00:00
-- url     : https://prove2.me/theorems/5d44c185-c8aa-4ab9-9973-e88f5b1950b1
-- title:
--   Pure endowment equals discounted survivor mass
-- statement:
--   Pure endowment equals discounted survivor mass.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[v^n\mathbf{1}_{\{K\ge n\}}]=v^nS(n)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_pure
import Definitions.Def_actuarial_c_pureMass

open ActuarialAssurances

theorem actuarial_c_pure_reconcile (h n : ℕ) (v : ℝ) (p : ℕ → ℝ) : pure h n v p=pureMass h n v p := by sorry
