-- Prove2me | Theorems.Thm_CouretOaiBridge01_InteriaSA04_besselPowerIntegrableAtZero_iff
-- name    : CouretOaiBridge01.InteriaSA04.besselPowerIntegrableAtZero_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:42.94979+00:00
-- url     : https://prove2.me/theorems/fd41587c-6c07-439d-9061-3f8b6b3491c1
-- title:
--   Integrability threshold for the Bessel model power
-- statement:
--   For every real $\nu$,
--
--   $$x\mapsto x^{1-2|\nu|}\text{ is Lebesgue integrable on }(0,1)\iff|\nu|<1.$$
--
--   These are strict endpoint power-integrability statements.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/8a8227048f12169067627c9a591ee5448bdfc0b9/research/lean/CouretOaiBridge01/INTERIA_SA_04_PowerIntegrability.lean#L23-L29, lines 23–29; source file SHA-256 cfac4fa678c7644bb2b685adf9e67098147f602e1a13561b1805959e09d41567; theorem CouretOaiBridge01.InteriaSA04.besselPowerIntegrableAtZero_iff

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

theorem besselPowerIntegrableAtZero_iff (nu : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (1 - 2 * |nu|)) (Ioo (0 : ℝ) 1) ↔ |nu| < 1 := by sorry












end CouretOaiBridge01.InteriaSA04
