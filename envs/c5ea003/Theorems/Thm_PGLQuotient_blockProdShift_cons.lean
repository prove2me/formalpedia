-- Prove2me | Theorems.Thm_PGLQuotient_blockProdShift_cons
-- name    : PGLQuotient.blockProdShift_cons
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:44:57.947193+00:00
-- url     : https://prove2.me/theorems/174a8c29-5792-4e3d-b553-8fffea1679d7
-- title:
--   BlockProdShift cons
-- statement:
--   Formal statement of `PGLQuotient.blockProdShift_cons` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PGLQuotient.blockProdShift_cons(q : ℝ) (j a : ℕ) (g : Vertex (n + 1)) :
--       blockProdShift q j (consV a g)
--         = (1 - q⁻¹ ^ (1 + j)) *
--           (if a = 0 then blockProdShift q (j + 1) g else blockProdShift q 0 g) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/TwistedWeight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/TwistedWeight.lean#L269

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

theorem PGLQuotient.blockProdShift_cons(q : ℝ) (j a : ℕ) (g : Vertex (n + 1)) :
    blockProdShift q j (consV a g)
      = (1 - q⁻¹ ^ (1 + j)) *
        (if a = 0 then blockProdShift q (j + 1) g else blockProdShift q 0 g) := by sorry
