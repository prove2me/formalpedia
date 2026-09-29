-- Prove2me | Theorems.Thm_TriangularForest_degree_second_le_two
-- name    : TriangularForest.degree_second_le_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:59:22.476918+00:00
-- url     : https://prove2.me/theorems/f4876a16-e296-48fa-96d2-01d88053fd96
-- title:
--   The second vertex of a longest path.
-- statement:
--   **The second vertex of a longest path.**  In a triangular forest, if `a → v₁ → v₂ → ⋯` is a
--   longest path and `a` is adjacent to `v₂`, then `v₁` has degree at most two.
--
--   ```lean
--   theorem TriangularForest.degree_second_le_two(hG : IsTriangularForest G)
--       {a v₁ v₂ b : V} (h₀₁ : G.Adj a v₁) (h₁₂ : G.Adj v₁ v₂) (r : G.Walk v₂ b)
--       (hp : (Walk.cons h₀₁ (Walk.cons h₁₂ r)).IsPath)
--       (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath →
--         q.length ≤ (Walk.cons h₀₁ (Walk.cons h₁₂ r)).length)
--       (ha₂ : G.Adj a v₂) : G.degree v₁ ≤ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/SharpBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/SharpBound.lean#L47

-- Thm stub generated from Logic/TriangularForest/SharpBound.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs

/-!
# The sharp sparsity bound for triangular forests

A connected triangular forest on `n` vertices with `t` triangular blocks has `n - 1 + t` edges
and `2t ≤ n - 1`, so `2e ≤ 3(n-1)`.  Here we prove this sharp bound
(`TriangularForest.two_mul_card_edgeFinset_le`) without developing block decompositions, by
refining the longest-path argument of `Logic.TriangularForest.Sparsity`:

* `TriangularForest.degree_second_le_two` — if `p = a → v₁ → v₂ → ⋯` is a longest path in a
  triangular forest and `a` is also adjacent to `v₂` (which happens as soon as `a` has degree
  two), then the *second* vertex `v₁` also has degree at most two.  Neighbours of `v₁` off the
  path would allow the reroute `y → v₁ → a → v₂ → ⋯`, which is longer; neighbours further along
  the path close a cycle of length `≥ 4`, except for the vertex `v₃`, which is excluded by the
  4-cycle `a → v₁ → v₃ → v₂ → a`.
* `TriangularForest.exists_adj_degree_le_two` — hence a triangular forest of minimum degree at
  least two contains an *edge* both of whose endpoints have degree two (a leaf triangle).
* Deleting such a pair removes two vertices and exactly three edges, which powers the induction
  giving `2e ≤ 3(n-1)`.

As a consequence `Kₙ` fails to decompose into two triangular forests already for `n ≥ 6`, which
combined with `TriangularForest.completeGraph_decomposesIntoTwo_five` pins the threshold
exactly: `Kₙ` decomposes into two triangular forests if and only if `n ≤ 5`.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}



variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem TriangularForest.degree_second_le_two(hG : IsTriangularForest G)
    {a v₁ v₂ b : V} (h₀₁ : G.Adj a v₁) (h₁₂ : G.Adj v₁ v₂) (r : G.Walk v₂ b)
    (hp : (Walk.cons h₀₁ (Walk.cons h₁₂ r)).IsPath)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsPath →
      q.length ≤ (Walk.cons h₀₁ (Walk.cons h₁₂ r)).length)
    (ha₂ : G.Adj a v₂) : G.degree v₁ ≤ 2 := by sorry
