-- Prove2me | Theorems.Thm_LeblRA_pointwise_subsequence_11_6_5
-- name    : LeblRA.pointwise_subsequence_11_6_5
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:41:19.419444+00:00
-- url     : https://prove2.me/theorems/6992d087-8688-46e1-9c27-682397205511
-- title:
--   Proposition 11.6.5 — Pointwise subsequence on a countable set
-- statement:
--   Let $X$ be any countable set and let $F_n:X\to\mathbb C$ be a sequence of functions. Assume pointwise boundedness:
--
--   $$\forall x\in X\;\exists M_x\in\mathbb R\;\forall n\in\mathbb N,\qquad |F_n(x)|\le M_x.$$
--
--   Then there exist a strictly increasing map $\varphi:\mathbb N\to\mathbb N$ and a function $f:X\to\mathbb C$ such that
--
--   $$\forall x\in X,\qquad F_{\varphi(n)}(x)\longrightarrow f(x)\quad(n\to\infty).$$
--
--   This is the countable-domain subsequence result in [Lebl’s Proposition 11.6.5](https://www.jirka.org/ra/html/sec_arzelaascoli.html#prop_subsequenceoncountableX).
--
--   **Formalization Note.** $X$ carries no topology, and no continuity assumption is made. Finite and empty sets are included. The formal sequence starts at zero rather than one; this is only a reindexing. Strict increase is represented by `StrictMono`, and the pointwise limit is explicit.
-- source:
--   Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II, §11.6, Proposition 11.6.5, https://www.jirka.org/ra/html/sec_arzelaascoli.html

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
theorem pointwise_subsequence_11_6_5 {X : Type u} [Countable X]
    (F : ℕ → X → ℂ) (hF : ∀ x, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (f : X → ℂ), StrictMono φ ∧
      ∀ x, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)) := by sorry
end LeblRA
