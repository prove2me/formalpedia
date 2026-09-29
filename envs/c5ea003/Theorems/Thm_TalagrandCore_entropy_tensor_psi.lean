-- Prove2me | Theorems.Thm_TalagrandCore_entropy_tensor_psi
-- name    : TalagrandCore.entropy_tensor_psi
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:58:48.022663+00:00
-- url     : https://prove2.me/theorems/4e4dd460-7a7c-4111-94ab-e533c6c46025
-- title:
--   Tensorized entropy inequality on a finite Bernoulli cube
-- statement:
--   Let $\mu_p$ be the product Bernoulli measure on a finite Boolean cube, let $Z$ be a real-valued function, and for each coordinate $x$ let $c_x$ be independent of that coordinate. With $\psi(u)=e^{-u}-1+u$, the entropy of $e^{\lambda Z}$ satisfies
--
--   $$
--   \lambda\,\mathbb E[Ze^{\lambda Z}]-\mathbb E[e^{\lambda Z}]\log\mathbb E[e^{\lambda Z}]
--   \le \sum_x\mathbb E\!\left[e^{\lambda Z}\psi\!\left(\lambda(Z-c_x)\right)\right].
--   $$
--
--   This is the finite-product entropy tensorization interface used by both tails of the Talagrand argument.
--
--   **Formalization Note** Expectations are exact weighted sums on the Boolean cube, and coordinate independence is expressed by `FiberConst`.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem entropy_tensor_psi (p : NNReal) (hp : p ≤ 1)
    (Z : (κ → Bool) → ℝ) (lam : ℝ)
    (c : κ → (κ → Bool) → ℝ) (hc : ∀ x, FiberConst x (c x)) :
    lam * Ex (p : ℝ) (fun ω => Z ω * Real.exp (lam * Z ω)) -
      Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω)) *
        Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω))) ≤
      ∑ x : κ, Ex (p : ℝ)
        (fun ω => Real.exp (lam * Z ω) * psi (lam * (Z ω - c x ω))) := by sorry

end TalagrandCore
