-- Prove2me | Definitions.Def_Algebra_PGLQuotient_TwistedWeight
-- name    : Algebra_PGLQuotient_TwistedWeight
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:29:00.919075+00:00
-- url     : https://prove2.me/theorems/4304662e-ad72-49e7-b1a8-1b36ce08872c
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_TwistedWeight
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.TwistedWeight`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/TwistedWeight.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
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

namespace PGLQuotient

open Finset

variable {d : ℕ}

/-- The top-row defect `σ(λ) = ∑_i (λ_0 - λ_i)`. -/
def sigmaExp (g : Vertex d) : ℕ := ∑ i ∈ range d, (lam g 0 - lam g i)

/-- The size `m(λ) = #{i : λ_i = λ_0}` of the block of maximal entries. -/
def firstBlockSize (g : Vertex d) : ℕ := ((range d).filter (fun i => lam g i = lam g 0)).card

/-- The Levi factor with the block ranks in the top block shifted by `j`. -/
noncomputable def blockProdShift (q : ℝ) (j : ℕ) (g : Vertex d) : ℝ :=
  ∏ i ∈ range d, (1 - q⁻¹ ^ (blockRank g i + (if lam g i = lam g 0 then j else 0)))

/-- The twisted vertex mass. -/
noncomputable def twWeight (q : ℝ) (c j : ℕ) (g : Vertex d) : ℝ :=
  (q ^ (endDim g + c * sigmaExp g + j * firstBlockSize g) * blockProdShift q j g)⁻¹

section Basic

variable {q : ℝ}








end Basic

section Peeling

variable {n : ℕ}

/-- Prepending a top gap `a` to a rank-`(n+1)` vertex gives a rank-`(n+2)` vertex. -/
def consV (a : ℕ) (g : Vertex (n + 1)) : Vertex (n + 2) := Fin.cons a g













variable {q : ℝ}



end Peeling

end PGLQuotient


