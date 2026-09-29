-- Prove2me | Theorems.Thm_LeblRA_arzela_ascoli_11_6_9
-- name    : LeblRA.arzela_ascoli_11_6_9
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:42:08.47328+00:00
-- url     : https://prove2.me/theorems/b166302d-bad5-41e1-a562-176ce3794ec8
-- title:
--   Theorem 11.6.9 — Arzelà–Ascoli theorem
-- statement:
--   Let $(X,d)$ be a compact metric space and let $F_n:X\to\mathbb C$ be continuous functions. Suppose that
--
--   $$\forall x\in X\;\exists M_x\in\mathbb R\;\forall n\in\mathbb N,\qquad |F_n(x)|\le M_x,$$
--
--   and that
--
--   $$\forall\varepsilon>0\;\exists\delta>0\;\forall x,y\in X\;\forall n\in\mathbb N,\qquad d(x,y)<\delta\Longrightarrow |F_n(x)-F_n(y)|<\varepsilon.$$
--
--   Then the sequence is uniformly bounded:
--
--   $$\exists M\in\mathbb R\;\forall n\in\mathbb N\;\forall x\in X,\qquad |F_n(x)|\le M,$$
--
--   and there exist a strictly increasing map $\varphi:\mathbb N\to\mathbb N$ and a continuous function $f:X\to\mathbb C$ such that $F_{\varphi(n)}$ converges uniformly to $f$. These are both conclusions of [Lebl’s Theorem 11.6.9, Arzelà–Ascoli](https://www.jirka.org/ra/html/sec_arzelaascoli.html#thm_arzelaascoli).
--
--   **Formalization Note.** Uniform boundedness is proved, not assumed. The subsequence index satisfies `StrictMono`; convergence is `TendstoUniformly`. Continuity of the limit is explicit, consistent with uniform convergence of continuous functions. Empty compact metric domains are allowed.
-- source:
--   Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II, §11.6, Theorem 11.6.9, https://www.jirka.org/ra/html/sec_arzelaascoli.html

import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
open Filter Set Topology
open scoped UniformConvergence
universe u

namespace LeblRA
theorem arzela_ascoli_11_6_9 {X : Type u} [MetricSpace X] [CompactSpace X]
    (F : ℕ → X → ℂ) (hF : ∀ n, Continuous (F n))
    (hb : ∀ x, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M)
    (he : ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ n, ‖F n x - F n y‖ < ε) :
    (∃ M : ℝ, ∀ n x, ‖F n x‖ ≤ M) ∧
    ∃ (φ : ℕ → ℕ) (f : X → ℂ), StrictMono φ ∧ Continuous f ∧
      TendstoUniformly (fun n => F (φ n)) f atTop := by sorry
end LeblRA
