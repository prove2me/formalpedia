-- Prove2me | Theorems.Thm_actuarial_d_independent_joint_survival
-- name    : actuarial_d_independent_joint_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:09:01.887993+00:00
-- url     : https://prove2.me/theorems/ee8d139a-92a5-4274-b42e-4b04327d5fa0
-- title:
--   Independence specialisation of joint survival
-- statement:
--   Independence specialisation of joint survival. Factorisation is established from the product joint probability kernel and normalised marginal death-year laws. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{xy}(t)=p_x(t)p_y(t)\quad\text{under independence}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_independentMass
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py

open ActuarialJointD

theorem actuarial_d_independent_joint_survival (h t : ℕ) (u v : ℕ → ℝ) (hu : (∑ i ∈ Finset.range (h+1), u i) = 1) (hv : (∑ j ∈ Finset.range (h+1), v j) = 1) : pxy h (independentMass u v) t = px h (independentMass u v) t * py h (independentMass u v) t := by sorry
