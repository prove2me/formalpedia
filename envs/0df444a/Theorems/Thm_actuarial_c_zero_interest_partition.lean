-- Prove2me | Theorems.Thm_actuarial_c_zero_interest_partition
-- name    : actuarial_c_zero_interest_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:26:46.62715+00:00
-- url     : https://prove2.me/theorems/0c2df7e2-3763-46d2-af82-8c7d81b57ab6
-- title:
--   No-interest conservation reduces to event probability partition
-- statement:
--   No-interest conservation reduces to event probability partition.
--
--   Mathematical relation:
--
--   $$
--   A^{1}_{n|}\big|_{v=1}+S(n)=1
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.7, general insurance–annuity identity, printed p. 71. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_pureMass

open ActuarialAssurances

theorem actuarial_c_zero_interest_partition (h n : ℕ) (p : ℕ → ℝ) (hn : n ≤ h) (hm : total h p=1) : term h n 1 (fun _ => 1) p+pureMass h n 1 p=1 := by sorry
