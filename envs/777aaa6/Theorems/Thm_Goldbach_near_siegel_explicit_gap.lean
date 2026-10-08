-- Prove2me | Theorems.Thm_Goldbach_near_siegel_explicit_gap
-- name    : Goldbach.near_siegel_explicit_gap
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T02:38:48.782932+00:00
-- url     : https://prove2.me/theorems/6c069107-c8b1-4a63-92d1-85ca34fa5f24
-- title:
--   An exact positive gap for the near-Siegel exponential majorant
-- statement:
--   For real numbers $0<c\le\lambda$, define
--   $$L(\lambda)=\max\left\{\frac{142}{25},\frac{109}{100}\log\frac1\lambda\right\},\qquad
--    \kappa(c)=\min\left\{\frac{54811}{10000}\min\left(c,\frac1{200}\right),\frac1{40}\right\}.$$
--   Then $\kappa(c)>0$ and
--   $$\exp\left(-\frac{33}{5}\lambda\right)
--    +202\exp\left(-\frac{164}{75}L(\lambda)\right)\le1-\kappa(c).$$
--
--   This is an explicit positive-gap bound for the exponential majorant appearing in the near-Siegel branch of [Lorenzo Schiavone's Goldbach exceptional-set manuscript](https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/), equations (7.18)–(7.21). The endpoint gap $1/40$ is weaker than the manuscript's reported constant. The elementary function inequality holds for all $\lambda\ge c>0$; the paper's analytic application has its own restricted defect range and additional hypotheses. There is no claim of a uniform positive gap as $c$ tends to zero.
--
--   The theorem does not derive the majorant from zeros of Dirichlet $L$-functions, establish an exceptional-set estimate, or resolve strong Goldbach.
--
--   Formalization note: The self-contained proof uses Mathlib revision `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e`, exact rational exponential estimates, and only standard axioms. No mathematical novelty is claimed.
-- source:
--   Elementary positive-gap step associated with equations (7.18)-(7.21), Lorenzo Schiavone: https://lorenzoschiavone.com/writing/goldbach-exceptional-set-bound/ . Uses weaker endpoint gap 1/40 and exact rational exponential bounds; no mathematical novelty or verification of analytic inputs is claimed.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false

theorem Goldbach.near_siegel_explicit_gap (c ell : ℝ) (hc : 0 < c) (hcell : c ≤ ell) :
    0 < min ((54811/10000)*min c (1/200)) (1/40) ∧
    Real.exp (-(33/5)*ell) +
      202*Real.exp (-(164/75)*max (142/25) ((109/100)*Real.log (1/ell))) ≤
      1-min ((54811/10000)*min c (1/200)) (1/40) := by sorry
