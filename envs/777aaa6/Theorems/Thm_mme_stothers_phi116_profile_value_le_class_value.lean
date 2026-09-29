-- Prove2me | Theorems.Thm_mme_stothers_phi116_profile_value_le_class_value
-- name    : mme_stothers_phi116_profile_value_le_class_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T07:31:43.833191+00:00
-- url     : https://prove2.me/theorems/bf9e601d-2b16-4b34-9bc6-df96ac3b5862
-- title:
--   Weighted profile value is bounded by the fifth class value
-- statement:
--   For the positive Davie--Stothers parameters $L(6,\tau)$ and $E(6,\tau)$ and any $0<a<1$, the optimized two-component profile value satisfies
--
--   $$4\left(\frac{2L(6,\tau)}{a}\right)^a\left(\frac{E(6,\tau)^2}{1-a}\right)^{1-a}\le 4\bigl(E(6,\tau)^2+2L(6,\tau)\bigr).$$
--
--   The right-hand side is the fifth class value in the source table. The inequality is the weighted arithmetic--geometric mean inequality and supplies the numerical bridge from the arbitrary profile parameter in the phi-116 frontier theorem to its class-value interface.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5, Lemma 5.1 and the fifth class-value entry; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data

open MME
universe u

theorem mme_stothers_phi116_profile_value_le_class_value
    (tau a : Real) (haPos : 0 < a) (haLt : a < 1) :
    4 * (((2 * MME.StothersFourth.L 6 tau) / a) ^ a *
      ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) ^ (1 - a)) ≤
      MME.StothersFourth.classValue 6 tau 5 := by
  sorry
