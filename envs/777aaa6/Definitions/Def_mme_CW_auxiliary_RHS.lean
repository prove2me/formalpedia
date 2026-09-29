-- Prove2me | Definitions.Def_mme_CW_auxiliary_RHS
-- name    : mme_CW_auxiliary_RHS
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-23T23:17:38.330015+00:00
-- url     : https://prove2.me/theorems/7fb6f8cc-0d09-45b7-a7ad-66e1f99e0d16
-- title:
--   Coppersmith--Winograd Section 8 auxiliary expression
-- statement:
--   **The Section 8 auxiliary expression** of Coppersmith–Winograd, with the exact $2.376$ certificate parameters.
--
--   Fix $q\in\mathbb{N}$ and reals $\tau$ and $a,b,c,d$. Here $\tau$ plays the role of $\omega/3$, and $a,b,c,d$ are the limiting frequencies with which the four block families of the regrouped tensor square $T_q^{\otimes 2}$ are used per symbol — $a$ for the scalar corner blocks, $b$ for the $\langle 1,1,2q\rangle$ products, $c$ for the $\langle 1,1,q^2{+}2\rangle$ products, and $d$ for the coupled central constituent (equation (13), journal pp. 268–269). The definition is the normalized right-hand side obtained on journal p. 269 after substituting these frequencies and taking $N$-th roots:
--
--   $$
--   \operatorname{auxiliaryRHS}(q,\tau,a,b,c,d)\;=\;\frac{(2q)^{6\tau b}\,\bigl(q^{2}+2\bigr)^{3\tau c}\,\bigl[4q^{3\tau}(q^{3\tau}+2)\bigr]^{d}}{(2a+2b+c)^{2a+2b+c}\,(2b+2d)^{2b+2d}\,(2c+d)^{2c+d}\,(2b)^{2b}\,a^{a}}.
--   $$
--
--   The numerator aggregates the values of the extracted blocks (the bracketed factor is the cubed symmetric value of the coupled constituent); the denominator is the entropy of the five marginal frequencies $A_0,\dots,A_4$ from equation (13). The laser extraction shows this quantity is at most $(q+2)^{2}$ at $\tau=\omega/3$, which is the engine of the $2.376$ bound.
--
--   The module also records the exact rational certificate parameters $a=233/10^{6}$, $b=12506/10^{6}$, $c=102546/10^{6}$, and $d=616627/(3\cdot 10^{6})$ — the printed optimizers on journal p. 269, with $d$ determined exactly by the normalization $3a+6b+3c+3d=1$ (its decimal expansion $0.205542\overline{3}$ rounds to the printed $0.205542$).
--
--   **Formalization Note** Real (`rpow`) exponentiation is used throughout, so the expression is meaningful for all real parameters; the constraint $3a+6b+3c+3d=1$ is *not* built into the definition — theorems assume it explicitly.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equation (13) and the auxiliary equation, journal pp. 268--269 (PDF pp. 18--19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Coppersmith--Winograd Section 8 auxiliary expression

This is the right-hand side obtained on journal p. 269 after substituting the
five marginal frequencies from equation (13) into the tensor-square laser
extraction and taking `N`-th roots.
-/

namespace MME

/-- The normalized Section 8 auxiliary right-hand side from CW90 journal
p. 269.  Real exponentiation is intentional throughout. -/
noncomputable def auxiliaryRHS
    (q : ℕ) (tau a b c d : ℝ) : ℝ :=
  ((2 * (q : ℝ)) ^ (6 * tau * b) *
      ((q : ℝ) ^ 2 + 2) ^ (3 * tau * c) *
      (4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)) ^ d) /
    ((2 * a + 2 * b + c) ^ (2 * a + 2 * b + c) *
      (2 * b + 2 * d) ^ (2 * b + 2 * d) *
      (2 * c + d) ^ (2 * c + d) *
      (2 * b) ^ (2 * b) * a ^ a)

/-! ## Exact rational parameters for the `2.376` certificate -/

/-- The printed value `0.000233` on CW90 journal p. 269, taken exactly. -/
noncomputable def cw2376_a : ℝ := 233 / 1000000

/-- The printed value `0.012506` on CW90 journal p. 269, taken exactly. -/
noncomputable def cw2376_b : ℝ := 12506 / 1000000

/-- The printed value `0.102546` on CW90 journal p. 269, taken exactly. -/
noncomputable def cw2376_c : ℝ := 102546 / 1000000

/-- The exact normalized value of `d` obtained from
`3a + 6b + 3c + 3d = 1`.  Its decimal expansion begins
`0.205542333...`, so it rounds to the paper's printed `0.205542`. -/
noncomputable def cw2376_d : ℝ := 616627 / 3000000

end MME


