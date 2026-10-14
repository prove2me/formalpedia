-- Prove2me | Theorems.Thm_actuarial_c_endowment_second_decomposition
-- name    : actuarial_c_endowment_second_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:28:53.948112+00:00
-- url     : https://prove2.me/theorems/723bca6a-5920-4d44-967f-c8e4f9d063bd
-- title:
--   The squared endowment PV separates insured deaths and maturity survival with no cross term
-- statement:
--   The squared endowment PV separates insured deaths and maturity survival with no cross term.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z_{\text{end}}^2]=\mathbb E[Z_n^2]+v^{2n}S(n)
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, benefit random present value as context, printed p. 62. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_termSecond
import Definitions.Def_actuarial_c_endowSecond

open ActuarialAssurances

theorem actuarial_c_endowment_second_decomposition (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : n ≤ h) : endowSecond h n v b p=termSecond h n v b p+v^(2*n)*surv h p n := by sorry
