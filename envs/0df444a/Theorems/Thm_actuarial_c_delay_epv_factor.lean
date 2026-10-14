-- Prove2me | Theorems.Thm_actuarial_c_delay_epv_factor
-- name    : actuarial_c_delay_epv_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:27:41.544975+00:00
-- url     : https://prove2.me/theorems/c0ed1a39-48ef-46db-9143-245325cfb5bb
-- title:
--   An added deterministic claims-processing lag discounts the insurance EPV
-- statement:
--   An added deterministic claims-processing lag discounts the insurance EPV.
--
--   Mathematical relation:
--
--   $$
--   A^{\text{delay}}(r)=v^{r}A
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.1, claim processing and payment timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_delayPath
import Definitions.Def_actuarial_c_delayEPV

open ActuarialAssurances

theorem actuarial_c_delay_epv_factor (h lag : ℕ) (v : ℝ) (b p : ℕ → ℝ) : delayEPV h lag v b p=v^lag*epv h v b p := by sorry
