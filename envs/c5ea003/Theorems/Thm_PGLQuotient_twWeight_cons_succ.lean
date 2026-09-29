-- Prove2me | Theorems.Thm_PGLQuotient_twWeight_cons_succ
-- name    : PGLQuotient.twWeight_cons_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:47:09.636956+00:00
-- url     : https://prove2.me/theorems/a512ed75-5f2d-40ac-9244-6c93075e50bf
-- title:
--   Peeling a top row with positive gap.
-- statement:
--   Peeling a top row with positive gap.
--
--   ```lean
--   theorem PGLQuotient.twWeight_cons_succ(hq : 1 < q) (c j a : ℕ) (g : Vertex (n + 1)) :
--       twWeight q c j (consV (a + 1) g)
--         = (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹
--           * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * twWeight q (c + 1) 0 g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/TwistedWeight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/TwistedWeight.lean#L314

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














variable {q : ℝ}

theorem PGLQuotient.twWeight_cons_succ(hq : 1 < q) (c j a : ℕ) (g : Vertex (n + 1)) :
    twWeight q c j (consV (a + 1) g)
      = (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹
        * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * twWeight q (c + 1) 0 g := by sorry
