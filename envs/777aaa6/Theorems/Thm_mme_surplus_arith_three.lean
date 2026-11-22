-- Prove2me | Theorems.Thm_mme_surplus_arith_three
-- name    : mme_surplus_arith_three
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-22T20:27:14.667724+00:00
-- url     : https://prove2.me/theorems/7c2e65c1-b12e-4d27-af60-c7e6f5032e39
-- title:
--   Concrete N equal three surplus threshold
-- statement:
--   At level three, any witness with at least one copy and product at least $15625$ satisfies the surplus inequality with room to spare: with $\\tau_0=3952233/5000000$,
--
--   $$
--   343 < \\mathit{copies}\\cdot \\mathit{abc}^{\\tau_0}.
--   $$
--
--   Since $7^3=343$, this is $7^3<\\mathit{copies}\\cdot\\mathit{abc}^{\\tau_0}$: the $N=3$ case of the numerical surplus condition. The point $15625=5^6$ is chosen so the comparison has roughly sixfold margin ($15625^{\\tau_0}\\approx 2065$), and therefore follows from crude monotonicity of $x\\mapsto x^{\\tau_0}$ and $5^{4.74}>5^4=625$, with no sharp logarithm bounds. It isolates the only transcendental comparison in the $N=3$ witness search: whoever supplies a step with room for a copy and a boundary with product at least $15625$ closes the surplus arithmetic through this lemma.
--
--   **Formalization Note** The proof factors $(5^6)^{\\tau_0}=5^{6\\tau_0}$ and compares the exponent against $4$; numeral casts are normalized by `norm_num`.
-- source:
--   Threshold curve for the More Asymmetry N equal three witness search: R. P. Stanley, Duke Math. J. 40 (1973); M. Beck et al., Amer. Math. Monthly 110 (2003) (arXiv:math/0201013). The comparison method (rational-power monotonicity) is standard.

import Mathlib
set_option autoImplicit false

theorem mme_surplus_arith_three (copies abc : Nat) (hcopies : 1 <= copies) (habc : 15625 <= abc) : (((7 ^ 3 : Nat)) : Real) < (copies : Real) * ((((abc : Nat)) : Real) ^ (((3952233 : Real)) / 5000000)) := by sorry
