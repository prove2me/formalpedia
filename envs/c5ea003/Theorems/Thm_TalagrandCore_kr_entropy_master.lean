-- Prove2me | Theorems.Thm_TalagrandCore_kr_entropy_master
-- name    : TalagrandCore.kr_entropy_master
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:39.056013+00:00
-- url     : https://prove2.me/theorems/1cf7e4b6-086a-43c3-bcc1-0e261e560e73
-- title:
--   Klein–Rio compensated-process master entropy inequality
-- statement:
--   For the compensated finite linear process $f_t=e^{-M_t}$, let $F(t)=\mathbb E f_t$ and $\phi(t)=\psi(t)\log\psi(t)$. Under the unit envelope and variance assumptions, whenever $t>0$ and $\phi(t)\le1$,
--
--   $$
--   \mathbb E[f_t\log f_t]-(1-\phi(t))F(t)\log F(t)
--   \le \psi(t)\sigma^2\bigl(1+(t-1)e^t\bigr)F(t).
--   $$
--
--   This is the finite-product, derivative-free form of the Klein–Rio master inequality assembled from their equations (4.13)–(4.20).
--
--   **Formalization Note** The canonical finite argmax defines the active compensated branch.
-- source:
--   T. Klein and E. Rio, Concentration around the mean for maxima of empirical processes, Annals of Probability 33 (2005), Sections 2 and 4, pp. 1060–1077, arXiv:math/0506594. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem kr_entropy_master (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {t : ℝ} (ht : 0 < t)
    (hφ : ((Real.exp (2 * t) + 1) / 2) *
      Real.log ((Real.exp (2 * t) + 1) / 2) ≤ 1) :
    Ex (p : ℝ) (fun ω => krf coeff (p : ℝ) t ω *
        Real.log (krf coeff (p : ℝ) t ω)) -
      (1 - ((Real.exp (2 * t) + 1) / 2) *
        Real.log ((Real.exp (2 * t) + 1) / 2)) *
        (krF coeff (p : ℝ) t * Real.log (krF coeff (p : ℝ) t)) ≤
      ((Real.exp (2 * t) + 1) / 2) * (sigmaSq * (1 + (t - 1) * Real.exp t)) *
        krF coeff (p : ℝ) t := by sorry

end TalagrandCore
