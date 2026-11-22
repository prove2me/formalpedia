-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5_cycle_bounds
-- name    : ZeroFreeRRG.Hardcore.lemma_5_5_cycle_bounds
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:53:31.075959+00:00
-- url     : https://prove2.me/theorems/3dd17d19-c472-4cd4-913b-68c2dd6cd922
-- title:
--   Lemma 5.5(4) — summable cycle factors and nonvanishing of 1 + δ_ℓ
-- statement:
--   Under the assumptions of Lemma 5.5, there is a complex disk $D_0$ about $t$ such that
--
--   $$\sum_{\ell\ge1}\lambda_\ell\sup_{z\in D_0}|\delta_\ell(z)|^2<\infty,$$
--
--   and $1+\delta_\ell(z)\ne0$ for every $\ell\ge3$ and $z\in D_0$. Here $\lambda_\ell=(d-1)^\ell/(2\ell)$ and $\delta_\ell(z)=\sum_{a\ge2}\kappa_a(z)^\ell$.
--
--   The proof in Appendix D.3 uses nonnegativity of $K_t$ to obtain $\sum_{a\ge2}|\kappa_a(t)|\le1$, then Condition 2 and continuity to get a uniform geometric bound $|\delta_\ell(z)|\le(|\Omega|-1)b^\ell$ with $b<(d-1)^{-1/2}$. This gives summability and nonvanishing for large $\ell$; the finitely many remaining $\ell\ge3$ are handled by continuity from the positive real lower bound $1+\delta_\ell(t)>0$.
--
--   **Formalization Note.** Uniform suprema are represented by a bounding sequence $\beta_\ell$; summability of $\lambda_\ell\beta_\ell$ is equivalent to the displayed supremum formulation.
-- source:
--   Chen, Wang, Zhang, arXiv:2610.40510 (held version), Lemma 5.5(4), printed p. 40; proof in Appendix D.3, printed pp. 72–73, using trace identity (38), printed p. 38.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical ComplexOrder
open Filter Topology AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- Lemma 5.5(4): uniform geometric bounds for the short-cycle factors and nonvanishing for lengths at least three. -/
theorem lemma_5_5_cycle_bounds (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ)
    (ht : m.Nontrivial t) (hκ : ∀ κ ∈ m.nonconstEig (t : ℂ), κ ≤ 0) (hC2 : Condition2 m d t) :
    ∃ R : ℝ, 0 < R ∧
      (∃ β : ℕ → ℝ, (∀ ℓ, ∀ z ∈ Metric.ball (t : ℂ) R, ‖deltaCyc m (ℓ + 1) z‖ ^ 2 ≤ β ℓ) ∧
          Summable (fun ℓ => lamCyc d (ℓ + 1) * β ℓ)) ∧
      (∀ ℓ : ℕ, 3 ≤ ℓ → ∀ z ∈ Metric.ball (t : ℂ) R, 1 + deltaCyc m ℓ z ≠ 0) := by sorry
