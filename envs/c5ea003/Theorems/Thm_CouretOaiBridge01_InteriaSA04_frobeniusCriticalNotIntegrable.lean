-- Prove2me | Theorems.Thm_CouretOaiBridge01_InteriaSA04_frobeniusCriticalNotIntegrable
-- name    : CouretOaiBridge01.InteriaSA04.frobeniusCriticalNotIntegrable
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:31.864817+00:00
-- url     : https://prove2.me/theorems/c31ebbce-d41a-4693-9f6d-688eead6f513
-- title:
--   The critical Frobenius model power is not integrable
-- statement:
--   The function $x\mapsto x^{2(-1/2)}$ is not Lebesgue integrable on $(0,1)$.
--
--   These are strict endpoint power-integrability statements.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/8a8227048f12169067627c9a591ee5448bdfc0b9/research/lean/CouretOaiBridge01/INTERIA_SA_04_PowerIntegrability.lean#L60-L66, lines 60–66; source file SHA-256 cfac4fa678c7644bb2b685adf9e67098147f602e1a13561b1805959e09d41567; theorem CouretOaiBridge01.InteriaSA04.frobeniusCriticalNotIntegrable

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic

/-!
# INTERIA-SA-04 / first analytic power-integrability gates

These theorems are genuine mathematical integrability statements on (0,1),
obtained from the existing mathlib theorem `integrableOn_Ioo_rpow_iff`.
They do not prove the full Weyl endpoint classification, identify operator
domains, or establish any Hilbert-Polya / Riemann-hypothesis claim.

The `x^(1-2*|nu|)` model is the real-power integrand associated with the
squared singular Bessel mode `x^(-|nu|)` under radial weight `x dx`.
The `x^(2*r)` model corresponds to a real Frobenius mode `x^r` squared.
Connecting these model integrands to differential operator solutions
requires separate formalized hypotheses and equivalences.
-/

open Set MeasureTheory intervalIntegral

namespace CouretOaiBridge01.InteriaSA04

theorem frobeniusCriticalNotIntegrable :
    ¬ IntegrableOn (fun x : ℝ => x ^ (2 * (-(1 / 2 : ℝ))))
      (Ioo (0 : ℝ) 1) := by sorry


end CouretOaiBridge01.InteriaSA04
