-- Prove2me | solution 1 for PGLQuotient.autOrder_rank_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:12:37.459787+00:00
-- url     : https://prove2.me/submissions/6e53b84a-ae3d-43ca-a839-9070c32a0681

-- Sol generated from Algebra/PGLQuotient/HeightZetaRankTwo.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_VertexModel

/-!
# Rank two: exact vertex volume and the height zeta function

For `d = 2` the standard arithmetic quotient is the ray `Γ \ X` of Serre's theory of trees:
the vertex `λ = (n, 0)` has stabiliser of order `|GL_2(F_q)|` for `n = 0` and
`(q-1)^2 q^{n+1}` for `n ≥ 1`.  We compute here, with no sorries:

* `autOrder_rank_two` : the exact stabiliser order;
* `heightZeta_rank_two` : the positive-moment height zeta function
  `Z(s) = ∑_λ α(λ)^s / |Aut λ|` in closed form for `s < 2`, exhibiting it as a *rational*
  function of `u = q^{s/2}`, namely
  `Z = 1/(q(q-1)(q^2-1)) + u/((q-1)^2 q (q-u))`,
  whose unique pole sits at `u = q`, i.e. exactly at `s = d = 2`;
* `vertexMass_rank_two`, `vertexVolume_rank_two` : the closed product form of the vertex
  volume, obtained by specialising to `s = 0`:
  `∑_λ 1/|Aut λ| = 2/((q-1)^2 (q^2-1))`, so the `PGL`-normalised vertex volume is
  `(q-1) ∑_λ 1/|Aut λ| = 2/((q-1)(q^2-1))`;
* `heightZeta_rank_two_unbounded` : `Z(s) → ∞` as `s ↑ 2`, i.e. the pole is genuine.
-/

open PGLQuotient

open Finset

variable {q : ℝ}

/-! ### Explicit rank-two data -/

lemma lam_rank_two_zero (g : Vertex 2) : lam g 0 = g 0 := by
  simp [lam, gapAt]

lemma lam_rank_two_one (g : Vertex 2) : lam g 1 = 0 := by
  simp [lam]


lemma endDim_rank_two (g : Vertex 2) : endDim g = if g 0 = 0 then 4 else g 0 + 3 := by
  simp only [endDim, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    lam_rank_two_zero, lam_rank_two_one]
  split <;> omega

lemma blockRank_rank_two_zero (g : Vertex 2) : blockRank g 0 = 1 := by
  simp [blockRank, Finset.filter_singleton]

lemma blockRank_rank_two_one (g : Vertex 2) : blockRank g 1 = if g 0 = 0 then 2 else 1 := by
  have hr : range (1 + 1) = ({0, 1} : Finset ℕ) := by decide
  unfold blockRank
  rw [hr, Finset.filter_insert, Finset.filter_singleton, lam_rank_two_zero, lam_rank_two_one]
  by_cases h : g 0 = 0 <;> simp [h]



/-! ### The height zeta function in rank two -/








open PGLQuotient in
theorem solution(hq : 1 < q) (g : Vertex 2) :
    autOrder q g = if g 0 = 0 then q * (q - 1) * (q ^ 2 - 1)
      else (q - 1) ^ 2 * q ^ (g 0 + 1) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  unfold autOrder
  rw [show (range 2) = {0, 1} from by decide, Finset.prod_insert (by decide),
    Finset.prod_singleton, blockRank_rank_two_zero, blockRank_rank_two_one, endDim_rank_two]
  by_cases h : g 0 = 0
  · rw [if_pos h, if_pos h, if_pos h]
    field_simp
  · rw [if_neg h, if_neg h, if_neg h]
    field_simp
    ring
