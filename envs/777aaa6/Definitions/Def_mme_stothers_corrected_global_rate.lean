-- Prove2me | Definitions.Def_mme_stothers_corrected_global_rate
-- name    : mme_stothers_corrected_global_rate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T15:15:52.024588+00:00
-- url     : https://prove2.me/theorems/7197d0e6-adeb-43d1-be4d-cc6b602983ca
-- title:
--   Stothers fourth-power rate with target-to-ambient entropy loss
-- statement:
--   Let $n_i$ be the ten Table-1 multiplicities, $v_i(q,\tau)$ the corresponding cubed constituent-value expressions, and $A=Qa/3$ the common marginal vector of the retained profile $a$. Define
--
--   $$
--   R_{\mathrm{corr}}(q,\tau,a,b)=\prod_{i=0}^{9}\left(v_i(q,\tau)^{a_i/3}b_i^{b_i}a_i^{-a_i}\right)^{n_i}\prod_{j=0}^{8}A_j^{-A_j}.
--   $$
--
--   For a positive same-marginal pair, $a$ is the retained joint profile and $b$ is the entropy-maximizing ambient profile. Writing $P(x)=\prod_i x_i^{n_i x_i}$, the entropy factor is $P(b)/P(a)$, the loss supplied by the finite target-to-ambient counting ratio in Equation (3.4) and the thesis derivation. The constituent exponents still use $a$.
--
--   This separately named definition corrects the reciprocal factor printed in Equation (5.3); it leaves the previously published rate unchanged. It asserts no tensor-value inequality. Real powers and division use their total Lean definitions for all natural $q$, real $\tau$, and real profiles, including non-feasible inputs.
-- source:
--   Davie and Stothers (2013), Improved Bound for Complexity of Matrix Multiplication, Equation (3.4), printed pp. 358–359, and comparison with Equation (5.3), printed p. 368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; Stothers (2010), On the Complexity of Matrix Multiplication, Chapter 4.2, printed pp. 78–81, https://era.ed.ac.uk/handle/1842/4734. The separately named rate uses the target/ambient entropy-loss orientation P(b)/P(a) from the derivation, correcting the reciprocal orientation printed in Eq. (5.3).

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

set_option autoImplicit false

namespace MME.StothersFourth

/-- The fourth-power rate with the target/ambient entropy loss from
Davie--Stothers Equation (3.4). The retained profile is `a`; `b` is the
positive entropy-maximizing profile in the same marginal fiber.
The constituent powers use `a`, while the entropy factor is
`entropyProduct b / entropyProduct a`.
This is a separately named rate; the existing `globalRate` is unchanged. -/
noncomputable def correctedGlobalRate
    (q : ℕ) (tau : ℝ) (a b : Fin 10 → ℝ) : ℝ :=
  (∏ i,
      (Real.rpow (classValue q tau i) (a i / 3) *
        Real.rpow (b i) (b i) *
        Real.rpow (a i) (-a i)) ^ classMultiplicity i) *
    ∏ j, Real.rpow (marginal a j) (-marginal a j)

end MME.StothersFourth


