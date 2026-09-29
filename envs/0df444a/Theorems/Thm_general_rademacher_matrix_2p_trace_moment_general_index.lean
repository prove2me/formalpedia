-- Prove2me | Theorems.Thm_general_rademacher_matrix_2p_trace_moment_general_index
-- name    : general_rademacher_matrix_2p_trace_moment_general_index
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T03:10:56.685142+00:00
-- url     : https://prove2.me/theorems/b492680c-5194-460b-8b4c-f92b6ec187c3
-- statement:
--   **General-index Rademacher matrix $2p$-trace-moment bound.** For a finite family of Hermitian matrices $H_c$ over an arbitrary finite index type $\mu$, indexed by $c \in \iota$, with the variance matrix $V = \sum_c H_c^2$ satisfying a quadratic-form domination $v^\top V v \le \text{normV}\cdot v^\top v$ for all $v$ (so $\lambda_{\max}(V) \le \text{normV}$), the symmetric Rademacher trace moment is bounded: $\mathbb{E}_\varepsilon \operatorname{tr}\big((\sum_c \varepsilon_c H_c)^{2p}\big) \le \tfrac{(2p)!}{2^p p!}\,\text{normV}^p\,|\mu|$. This lifts the standard $\operatorname{Fin} d$ Tropp/Khintchine engine to an arbitrary finite index $\mu$ via a reindexing equivalence $\mu \simeq \operatorname{Fin}|\mu|$ (trace and powers are reindex-invariant), and supplies the engine's eigenvalue hypothesis from the quadratic-form bound. Proof (reduction): reindex $V$ and each $H_c$ to $\operatorname{Fin}|\mu|$, convert the quadratic-form bound to the eigenvalue bound via the Rayleigh bridge, apply the $\operatorname{Fin} d$ engine, and pull the trace moment back unchanged.
-- source:
--   Candes-Recht 2009 (arXiv:0805.4471) Sec 6.1 / Tropp matrix concentration. The Rademacher symmetric matrix trace-moment bound (Khintchine/Tropp engine) lifted from the Fin d index to an arbitrary finite index type μ via a reindexing equivalence μ ≃ Fin (card μ). The eigenvalue hypothesis of the Fin-d engine is supplied here from a quadratic-form domination of the variance matrix ∑ Hc² (which is how the block-diagonal variance matrix is bounded in the dilation application).

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Nat.Factorial.Basic
open Matrix
open scoped BigOperators

theorem general_rademacher_matrix_2p_trace_moment_general_index {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Type*} [Fintype μ] [DecidableEq μ] (H : ι → Matrix μ μ ℝ) (hHerm : ∀ c, (H c).IsHermitian) (normV : ℝ) (hnormVnn : 0 ≤ normV) (hVHerm : (∑ c : ι, H c * H c).IsHermitian) (hquad : ∀ v : μ → ℝ, (star v ⬝ᵥ (∑ c : ι, H c * H c) *ᵥ v) ≤ normV * (star v ⬝ᵥ v)) (p : ℕ) : (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) * Matrix.trace ((∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c) ^ (2 * p))) ≤ ((Nat.factorial (2 * p) : ℝ) / ((2 ^ p : ℝ) * (Nat.factorial p : ℝ))) * normV ^ p * (Fintype.card μ : ℝ) := by sorry
