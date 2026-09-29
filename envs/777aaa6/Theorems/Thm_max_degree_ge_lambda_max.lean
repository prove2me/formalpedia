-- Prove2me | Theorems.Thm_max_degree_ge_lambda_max
-- name    : max_degree_ge_lambda_max
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-04-23T04:02:08.011891+00:00
-- url     : https://prove2.me/theorems/59bab314-6386-49c1-97fc-0d09bced98ed
-- statement:
--   **Lemma 2.3 (max-degree spectral bound).** For any Hermitian matrix $A$ over a finite vertex set $V$ with entries in $\{-1, 0, 1\}$, whose zero pattern respects a decidable adjacency relation $\mathrm{adj}$ (i.e. $A_{uv} = 0$ whenever $u$ and $v$ are non-adjacent), there exists a vertex $v$ whose degree is at least the largest eigenvalue of $A$:
--
--   $$\lambda_{\max}(A) \;\le\; \bigl|\{\, u : \mathrm{adj}\ u\ v \,\}\bigr|.$$
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the sensitivity conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

/-!
# Lemma 2.3 — Max-degree spectral bound (generic)

Huang 2019, Lemma 2.3: if `G` is a graph on vertex set `V` and `A` is a symmetric
matrix indexed by `V` with entries in `{−1, 0, +1}` such that `A[u,v] = 0` whenever
`u` and `v` are non-adjacent in `G`, then `Δ(G) ≥ λ_max(A)`.

Stated here with a **plain adjacency predicate** `adj : V → V → Prop` instead of
a `SimpleGraph` — this keeps the lemma directly applicable to our hypercube
subset without building a `SimpleGraph` object. A `SimpleGraph`-flavored wrapper
can be added as a separate theorem later.
-/

/-- **Lemma 2.3 — Max-degree spectral bound (generic).**
For any Hermitian `A : Matrix V V ℝ` whose entries lie in `{−1, 0, 1}` and whose
zero pattern respects a decidable adjacency `adj` (i.e. `A[u,v] = 0` whenever
`u` and `v` are non-adjacent), there exists a vertex `v` with
`λ_max(A) ≤ #{u : adj u v}`. -/

theorem max_degree_ge_lambda_max
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (h_entries : ∀ u v : V, A u v = -1 ∨ A u v = 0 ∨ A u v = 1)
    (adj : V → V → Prop) [DecidableRel adj]
    (h_zero : ∀ u v : V, ¬ adj u v → A u v = 0)
    [Nonempty V] :
    ∃ v : V, hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩
      ≤ ((Finset.univ : Finset V).filter fun u => adj u v).card := by sorry
