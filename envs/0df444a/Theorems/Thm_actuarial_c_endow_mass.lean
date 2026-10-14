-- Prove2me | Theorems.Thm_actuarial_c_endow_mass
-- name    : actuarial_c_endow_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:21:10.244516+00:00
-- url     : https://prove2.me/theorems/20acdf21-0fe2-441c-b92f-d8d25779844b
-- title:
--   Death masses and pure-endowment survival make total endowment EPV
-- statement:
--   Death masses and pure-endowment survival make total endowment EPV.
--
--   Mathematical relation:
--
--   $$
--   A^{\text{end}}_{n|}=\sum_{j=0}^{n-1}v^{j+1}b_jp_j+v^nS(n)
--   $$
--
--   For this statement, the yearly death event, valuation origin and life-law normalisation follow the stated hypotheses. Death benefits are settled at the end of the policy year, whereas a maturity amount is payable at its anniversary. Every formula represents a currently open formal obligation unless it is a definition.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.4, endowment insurance, printed p. 65. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow

open ActuarialAssurances

theorem actuarial_c_endow_mass (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) : endow h n v b p=(∑ j ∈ Finset.range n, v^(j+1)*b j*p j)+v^n*surv h p n := by sorry
