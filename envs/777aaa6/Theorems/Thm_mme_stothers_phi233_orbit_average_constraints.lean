-- Prove2me | Theorems.Thm_mme_stothers_phi233_orbit_average_constraints
-- name    : mme_stothers_phi233_orbit_average_constraints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:05:50.718356+00:00
-- url     : https://prove2.me/theorems/800f2298-c6ec-4e73-a6ac-ace3df0727b7
-- title:
--   Same marginals force the phi_233 orbit-average constraints
-- statement:
--   Let $x_0,\ldots,x_9$ be a normalized profile on the ten ordered $\varphi_{233}$ joint types. Suppose its total mass is one and its selected first-, second-, and third-mode marginals agree with the Davie--Stothers parameters $\sigma$ and $\mu$. For the four symmetry-orbit parameters\n\n$$\na=\frac{x_0+x_2+x_7+x_9}{2},\qquad b=x_1+x_8,\qquad c=x_3+x_6,\qquad d=x_4+x_5,\n$$\n\none then has\n\n$$\n2a+b+c+d=1,\qquad 2a+b=\sigma,\qquad a+c=\mu.\n$$\n\nThis is the affine reduction from an arbitrary same-marginal completion profile to the four-parameter symmetric fibre used in the exceptional $\varphi_{233}$ entropy calculation.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 profile equations preceding Equation (3.6), pp. 359--360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_orbit_average_constraints
    (x : Fin 10 → ℝ) (sigma mu : ℝ)
    (htotal : ∑ r : Fin 10, x r = 1)
    (hsigma0 : x 0 + x 1 + x 2 = sigma / 2)
    (hsigma2 : x 7 + x 8 + x 9 = sigma / 2)
    (hmuJ0 : x 3 + x 7 = mu / 2)
    (hmuJ3 : x 2 + x 6 = mu / 2)
    (hmuK0 : x 6 + x 9 = mu / 2)
    (hmuK3 : x 0 + x 3 = mu / 2) :
    let a := (x 0 + x 2 + x 7 + x 9) / 2
    let b := x 1 + x 8
    let c := x 3 + x 6
    let d := x 4 + x 5
    2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu := by
  sorry
