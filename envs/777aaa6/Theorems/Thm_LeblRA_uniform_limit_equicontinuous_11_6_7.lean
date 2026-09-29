-- Prove2me | Theorems.Thm_LeblRA_uniform_limit_equicontinuous_11_6_7
-- name    : LeblRA.uniform_limit_equicontinuous_11_6_7
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:41:46.08242+00:00
-- url     : https://prove2.me/theorems/6bd7d6e0-7f06-4e09-a445-93a6e0b152ac
-- title:
--   Proposition 11.6.7 — Uniform convergence implies uniform equicontinuity
-- statement:
--   Let $(X,d)$ be a compact metric space, and let $F_n:X\to\mathbb C$ be continuous functions converging uniformly to $f:X\to\mathbb C$. Then the sequence is uniformly equicontinuous:
--
--   $$\forall\varepsilon>0\;\exists\delta>0\;\forall x,y\in X\;\forall n\in\mathbb N,\qquad d(x,y)<\delta\Longrightarrow |F_n(x)-F_n(y)|<\varepsilon.$$
--
--   Thus uniform convergence imposes one continuity condition shared by the entire sequence. This is [Lebl’s Proposition 11.6.7](https://www.jirka.org/ra/html/sec_arzelaascoli.html#sec_arzelaascoli-16).
--
--   **Formalization Note.** The full condition is written out: $\delta$ is independent of $n$, $x$, and $y$. Uniform convergence is `TendstoUniformly`. No boundedness or nonemptiness assumption is added.
-- source:
--   Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II, §11.6, Proposition 11.6.7, https://www.jirka.org/ra/html/sec_arzelaascoli.html

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
theorem uniform_limit_equicontinuous_11_6_7 {X : Type u} [MetricSpace X] [CompactSpace X]
    (F : ℕ → X → ℂ) (hF : ∀ n, Continuous (F n)) (f : X → ℂ)
    (hf : TendstoUniformly F f atTop) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ n, ‖F n x - F n y‖ < ε := by sorry
end LeblRA
