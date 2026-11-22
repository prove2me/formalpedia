-- Prove2me | Theorems.Thm_mme_surplus_arith_four
-- name    : mme_surplus_arith_four
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-22T21:29:08.76349+00:00
-- url     : https://prove2.me/theorems/121e85a4-5083-4924-84a5-4bb0c2b6fb69
-- title:
--   Concrete N equal four surplus threshold
-- statement:
--   At level four, any witness with at least one copy and product at least $390625$ satisfies the surplus inequality with room to spare: with $\\tau_0=3952233/5000000$,
--
--   $$
--   2401 < \\mathit{copies}\\cdot \\mathit{abc}^{\\tau_0}.
--   $$
--
--   Since $7^4=2401$ and $390625=5^8$, this is $5^{8\\tau_0}\\ge 5^6=15625>2401$ by monotonicity ($8\\tau_0\\approx 6.33>6$), scaled by the copy and product hypotheses. Level four is the least feasible level: levels are even ($L\\cdot 2^{\\ell-1}=N$ with even $L$), so the level-three analogue is vacuous. It isolates the only transcendental comparison in the $N=4$ witness search.
--
--   **Formalization Note** The proof factors $(5^8)^{\\tau_0}=5^{8\\tau_0}$ and compares the exponent against $6$; numeral casts are normalized by `norm_num`.
-- source:
--   Threshold curve for the More Asymmetry N equal four witness search (least feasible level): R. P. Stanley, Duke Math. J. 40 (1973); M. Beck et al., Amer. Math. Monthly 110 (2003) (arXiv:math/0201013).

import Mathlib
set_option autoImplicit false

theorem mme_surplus_arith_four (copies abc : Nat) (hcopies : 1 <= copies) (habc : 390625 <= abc) : (((7 ^ 4 : Nat)) : Real) < (copies : Real) * ((((abc : Nat)) : Real) ^ (((3952233 : Real)) / 5000000)) := by sorry
