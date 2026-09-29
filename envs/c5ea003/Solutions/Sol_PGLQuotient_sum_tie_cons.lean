-- Prove2me | solution 1 for PGLQuotient.sum_tie_cons
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:32:21.434794+00:00
-- url     : https://prove2.me/submissions/0d7a27a3-d84a-4089-8866-f3fd1845d22a

-- Sol generated from Algebra/PGLQuotient/TwistedWeight.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_lam_antitone

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





open PGLQuotient in
theorem solution(a : ℕ) (g : Vertex (n + 1)) :
    ∑ i ∈ range (n + 1), (lam g i + 1 - (a + lam g 0))
      = (if a = 0 then firstBlockSize g else 0) := by
  have hterm : ∀ i ∈ range (n + 1),
      lam g i + 1 - (a + lam g 0) = (if lam g i = a + lam g 0 then 1 else 0) := by
    intro i _
    have := lam_antitone g (Nat.zero_le i)
    by_cases h : lam g i = a + lam g 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [Finset.sum_congr rfl hterm]
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    unfold firstBlockSize
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.zero_add])
  · rw [if_neg ha]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have := lam_antitone g (Nat.zero_le i)
    rw [if_neg (by omega)]
