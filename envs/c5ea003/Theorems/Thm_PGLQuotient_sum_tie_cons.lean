-- Prove2me | Theorems.Thm_PGLQuotient_sum_tie_cons
-- name    : PGLQuotient.sum_tie_cons
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:47:03.66272+00:00
-- url     : https://prove2.me/theorems/0a6d3386-07c0-4a97-a169-10f5ac617e9f
-- title:
--   The number of rows of `λ'` tied with the top row, seen from the prepended row.
-- statement:
--   The number of rows of `λ'` tied with the top row, seen from the prepended row.
--
--   ```lean
--   theorem PGLQuotient.sum_tie_cons(a : ℕ) (g : Vertex (n + 1)) :
--       ∑ i ∈ range (n + 1), (lam g i + 1 - (a + lam g 0))
--         = (if a = 0 then firstBlockSize g else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/TwistedWeight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/TwistedWeight.lean#L188

-- Thm stub generated from Algebra/PGLQuotient/TwistedWeight.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel

/-!
# The twisted vertex mass and its row-peeling recursion

To compute the vertex volume of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))`
in arbitrary rank we enlarge the vertex mass `1/|Aut λ|` to a two-parameter family.

For a vertex `λ` of rank `d` (in the gap model of `Algebra.PGLQuotient.VertexModel`) put

* `sigmaExp λ = ∑_i (λ_0 - λ_i)` — the "top-row defect";
* `firstBlockSize λ = #{ i : λ_i = λ_0 }` — the size of the block of maximal entries;
* `blockProdShift q j λ = ∏_i (1 - q^{-(r_i + j·[λ_i = λ_0])})` — the Levi factor with the
  ranks in the top block shifted by `j`;
* `twWeight q c j λ = (q^{dim End + c·σ + j·m} · blockProdShift q j λ)⁻¹`.

For `c = j = 0` this is exactly the vertex mass: `twWeight q 0 0 = vertexWeight q`
(`twWeight_zero_zero`).

The point of the two extra parameters is that the family is *stable under peeling off the top
row of `λ`*: writing a rank-`(n+2)` vertex as `Fin.cons a λ'` with `a = λ_0 - λ_1 ≥ 0` the gap
between the first row and the rest, one gets (`twWeight_cons_zero`, `twWeight_cons_succ`)

`twWeight q c j (cons 0 λ') = K · twWeight q (c+1) (j+1) λ'`,
`twWeight q c j (cons (a+1) λ') = K · q^{-(n+1)(c+1)(a+1)} · twWeight q (c+1) 0 λ'`,

with `K = (q^{n+2+j}(1 - q^{-(1+j)}))⁻¹`.  This is the recursion which, summed over all
vertices, produces the closed product form of the vertex volume.
-/

open PGLQuotient

open Finset

variable {d : ℕ}






variable {q : ℝ}










variable {n : ℕ}

theorem PGLQuotient.sum_tie_cons(a : ℕ) (g : Vertex (n + 1)) :
    ∑ i ∈ range (n + 1), (lam g i + 1 - (a + lam g 0))
      = (if a = 0 then firstBlockSize g else 0) := by sorry
