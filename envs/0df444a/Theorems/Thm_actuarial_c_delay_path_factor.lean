-- Prove2me | Theorems.Thm_actuarial_c_delay_path_factor
-- name    : actuarial_c_delay_path_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T21:27:26.106222+00:00
-- url     : https://prove2.me/theorems/3a57f8ec-4cfa-4717-959d-4cb79ace47f6
-- title:
--   At each realised lifetime state a deterministic extra settlement lag multiplies the claim PV
-- statement:
--   At each realised lifetime state a deterministic extra settlement lag multiplies the claim PV.
--
--   Mathematical relation:
--
--   $$
--   Z^{\text{delay}}_{r}(K)=v^{r}Z(K)
--   $$
--
--   The declared assumptions restrict the life law, discount and coverage exactly as required. This is an open actuarial theorem, derived from realised claim events or their expected values.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.1, claim processing and payment timing, printed p. 61. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_delayPath

open ActuarialAssurances

theorem actuarial_c_delay_path_factor (h lag k : ℕ) (v : ℝ) (b : ℕ → ℝ) : delayPath h lag v b k=v^lag*path h v b k := by sorry
