-- Prove2me | solution 1 for PGLQuotient.vertexMass_rank_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:47:58.023794+00:00
-- url     : https://prove2.me/submissions/071b0bac-7baf-472d-a959-0f4f0824eb49

-- Sol generated from Algebra/PGLQuotient/HeightZetaRankTwo.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_heightZeta_rank_two

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









/-! ### The height zeta function in rank two -/








open PGLQuotient in
theorem solution(hq : 1 < q) :
    ∑' g : Vertex 2, vertexWeight q g = 2 / ((q - 1) ^ 2 * (q ^ 2 - 1)) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hq1 : q - 1 ≠ 0 := by
    have : (0:ℝ) < q - 1 := by linarith
    exact ne_of_gt this
  have hq2 : q ^ 2 - 1 ≠ 0 := by
    have : (1:ℝ) < q ^ 2 := by nlinarith
    exact ne_of_gt (by linarith)
  have h := heightZeta_rank_two (q := q) hq (s := 0) (by norm_num)
  have hz : heightZeta q 2 0 = ∑' g : Vertex 2, vertexWeight q g := by
    unfold heightZeta
    refine tsum_congr (fun g => ?_)
    rw [Real.rpow_zero, mul_one]
  rw [hz] at h
  rw [h]
  simp only [zero_div, Real.rpow_zero]
  field_simp
  ring
