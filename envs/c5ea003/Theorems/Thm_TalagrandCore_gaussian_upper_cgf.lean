-- Prove2me | Theorems.Thm_TalagrandCore_gaussian_upper_cgf
-- name    : TalagrandCore.gaussian_upper_cgf
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:04.640056+00:00
-- url     : https://prove2.me/theorems/c91bd999-6238-4668-a96b-4baceb092c2d
-- title:
--   Gaussian-regime cumulant bound for a finite linear supremum
-- statement:
--   Let $Z$ be a centered finite Bernoulli linear supremum with coefficient envelope one, variance proxy $\sigma^2$, random variance process $\Sigma^2$, and absolute supremum $\bar Z$. For $0\le\lambda\le1/8$,
--
--   $$
--   \log\mathbb E e^{\lambda(Z-\mathbb EZ)}
--   \le 200\lambda^2\left(\sigma^2+\mathbb E\Sigma^2+\mathbb E\bar Z\right).
--   $$
--
--   This is the small-deviation Gaussian part of the upper-tail proof.
--
--   **Formalization Note** All expectations are finite Bernoulli weighted sums.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem gaussian_upper_cgf (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ) (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (lam : ℝ) (h0 : 0 ≤ lam) (h8 : lam ≤ 1/8) :
    Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam *
        (Zproc coeff (p : ℝ) ω - Ex (p : ℝ) (Zproc coeff (p : ℝ)))))) ≤
      200 * lam ^ 2 *
        (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ))) := by sorry

end TalagrandCore
