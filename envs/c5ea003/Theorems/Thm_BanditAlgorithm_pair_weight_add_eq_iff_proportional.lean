-- Prove2me | Theorems.Thm_BanditAlgorithm_pair_weight_add_eq_iff_proportional
-- name    : BanditAlgorithm.pair_weight_add_eq_iff_proportional
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T04:18:20.205787+00:00
-- url     : https://prove2.me/theorems/0737cb34-6c01-47f3-96cf-0bb52880f694
-- title:
--   Equality in the superadditivity of $\tfrac{xy}{x+y}$ iff proportional
-- statement:
--   For positive reals, equality holds in the superadditivity of $h(x,y)=xy/(x+y)$,
--   $$\frac{x_1y_1}{x_1+y_1}+\frac{x_2y_2}{x_2+y_2}=\frac{(x_1+x_2)(y_1+y_2)}{(x_1+x_2)+(y_1+y_2)},$$
--   **if and only if** $x_1y_2=x_2y_1$, that is, if and only if $(x_1,y_1)$ and $(x_2,y_2)$ lie on a common ray through the origin.
--
--   Both directions follow from the polynomial identity
--   $$(x_1+x_2)(y_1+y_2)(x_1+y_1)(x_2+y_2)-\big(x_1y_1(x_2+y_2)+x_2y_2(x_1+y_1)\big)\big((x_1+x_2)+(y_1+y_2)\big)=(x_1y_2-x_2y_1)^2,$$
--   after clearing the (positive) denominators.
--
--   Since $h$ is homogeneous of degree one it is genuinely linear along each ray, so no concavity statement about it can be strict in every direction; proportionality is exactly the degenerate direction, and the statement above says it is the only one. That dichotomy is what upgrades convexity of the set of maximisers of $\min_{j\ne i}h(\alpha_i,\alpha_j)(\mu_i-\mu_j)^2/2$ to uniqueness: two maximisers would have to satisfy $\alpha_i\beta_j=\beta_i\alpha_j$ for every $j$, hence be proportional, and two proportional probability vectors are equal.
-- source:
--   Equality case of the superadditivity of the parallel sum; the strict-concavity-transverse-to-rays statement underlying uniqueness of the optimal allocation in Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Lemma 4.

import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem BanditAlgorithm.pair_weight_add_eq_iff_proportional {x₁ y₁ x₂ y₂ : ℝ}
    (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    (x₁ * y₁ / (x₁ + y₁) + x₂ * y₂ / (x₂ + y₂)
        = (x₁ + x₂) * (y₁ + y₂) / ((x₁ + x₂) + (y₁ + y₂)))
      ↔ x₁ * y₂ = x₂ * y₁ := by
  sorry
