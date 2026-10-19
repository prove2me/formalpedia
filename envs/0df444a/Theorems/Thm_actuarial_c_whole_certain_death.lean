-- Prove2me | Theorems.Thm_actuarial_c_whole_certain_death
-- name    : actuarial_c_whole_certain_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:27:03.57199+00:00
-- url     : https://prove2.me/theorems/1b931de9-8929-405d-974c-2d6ca19c6b29
-- title:
--   Classical annual whole-life identity requires no censored survivor mass
-- statement:
--   Classical annual whole-life identity requires no censored survivor mass.
--
--   Mathematical relation:
--
--   $$
--   S(h)=0\Longrightarrow A_h+(1-v)\ddot a_h=1
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
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_due

open ActuarialAssurances

theorem actuarial_c_whole_certain_death (h : ℕ) (v : ℝ) (p : ℕ → ℝ) (hm : total h p=1) (ht : p h = 0) : epv h v (fun _ => 1) p+(1-v)*due h h v p=1 := by sorry
