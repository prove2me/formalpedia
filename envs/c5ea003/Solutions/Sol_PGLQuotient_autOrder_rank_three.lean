-- Prove2me | solution 1 for PGLQuotient.autOrder_rank_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:12:36.96309+00:00
-- url     : https://prove2.me/submissions/79a73ad2-9055-4ac6-a853-db2313a964ca

-- Sol generated from Algebra/PGLQuotient/VertexVolumeRankThree.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Definitions.Def_Algebra_PGLQuotient_VertexVolumeRankThree

/-!
# Rank three: the exact vertex volume in closed product form

We evaluate, with no sorries, the total vertex mass of the standard arithmetic quotient
of the affine Bruhat–Tits building of `PGL_3(F_q((t^{-1})))`:

`∑_λ 1/|Aut λ| = 3 / ((q-1)^2 (q^2-1)^2 (q^3-1)) = 3 / (P(3) P(2))`,

where `P(m) = ∏_{k=1}^m (q^k - 1)`.  Equivalently the `PGL`-normalised vertex volume is
`(q-1) ∑_λ 1/|Aut λ| = 3/((q-1)(q^2-1)^2(q^3-1))`.

This is the `d = 3` instance of the conjectured closed product form
`d (q-1) / (P(d) P(d-1))` (see `FUTURE_DIRECTIONS.md`); the `d = 2` instance is
`vertexVolume_rank_two`.

The proof is the building-theoretic one: vertices are parametrised by the dominant sector
(here `ℕ^2` in gap coordinates), the stabiliser orders are computed *exactly* in the four
strata `g = (0,0)`, `(0,b)`, `(a,0)`, `(a,b)` cut out by the vanishing of the gaps, and the
resulting sum over the strata (the `d = 3` "cut-set" decomposition) is summed as a double
geometric series.
-/

open PGLQuotient

open Finset

variable {q : ℝ}

/-! ### A geometric summation helper -/



/-! ### Explicit rank-three data -/

lemma lam_rank_three_zero (g : Vertex 3) : lam g 0 = g 0 + g 1 := by
  have h : Finset.Ico 0 (3 - 1) = ({0, 1} : Finset ℕ) := by decide
  simp [lam, h, gapAt]

lemma lam_rank_three_one (g : Vertex 3) : lam g 1 = g 1 := by
  have h : Finset.Ico 1 (3 - 1) = ({1} : Finset ℕ) := by decide
  simp [lam, h, gapAt]

lemma lam_rank_three_two (g : Vertex 3) : lam g 2 = 0 := by
  simp [lam]

/-- `dim End(⨁ O(λ_i))` for `d = 3`, in the four strata. -/
lemma endDim_rank_three (g : Vertex 3) :
    endDim g = if g 0 = 0 then (if g 1 = 0 then 9 else 2 * g 1 + 7)
      else (if g 1 = 0 then 2 * g 0 + 7 else 2 * g 0 + 2 * g 1 + 6) := by
  simp only [endDim, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    lam_rank_three_zero, lam_rank_three_one, lam_rank_three_two]
  split_ifs <;> omega

lemma blockRank_rank_three_zero (g : Vertex 3) : blockRank g 0 = 1 := by
  simp [blockRank, Finset.filter_singleton]

lemma blockRank_rank_three_one (g : Vertex 3) :
    blockRank g 1 = if g 0 = 0 then 2 else 1 := by
  have hr : range (1 + 1) = ({0, 1} : Finset ℕ) := by decide
  unfold blockRank
  rw [hr, Finset.filter_insert, Finset.filter_singleton, lam_rank_three_zero,
    lam_rank_three_one]
  by_cases h : g 0 = 0 <;> simp [h]

lemma blockRank_rank_three_two (g : Vertex 3) :
    blockRank g 2 = if g 1 = 0 then (if g 0 = 0 then 3 else 2) else 1 := by
  have hr : range (2 + 1) = ({0, 1, 2} : Finset ℕ) := by decide
  unfold blockRank
  rw [hr, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
    lam_rank_three_zero, lam_rank_three_one, lam_rank_three_two]
  by_cases h0 : g 0 = 0 <;> by_cases h1 : g 1 = 0 <;>
    simp [h0, h1]




/-! ### Summing over the dominant sector -/






theorem solution(hq : 1 < q) (g : Vertex 3) :
    autOrder q g =
      if g 0 = 0 then
        (if g 1 = 0 then q ^ 3 * (q - 1) * (q ^ 2 - 1) * (q ^ 3 - 1)
         else q ^ (2 * g 1 + 3) * (q - 1) ^ 2 * (q ^ 2 - 1))
      else
        (if g 1 = 0 then q ^ (2 * g 0 + 3) * (q - 1) ^ 2 * (q ^ 2 - 1)
         else q ^ (2 * g 0 + 2 * g 1 + 3) * (q - 1) ^ 3) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  unfold autOrder
  rw [show (range 3) = {0, 1, 2} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, blockRank_rank_three_zero,
    blockRank_rank_three_one, blockRank_rank_three_two, endDim_rank_three]
  by_cases h0 : g 0 = 0 <;> by_cases h1 : g 1 = 0
  · simp only [if_pos h0, if_pos h1]
    field_simp
  · simp only [if_pos h0, if_neg h1]
    rw [show 2 * g 1 + 7 = (2 * g 1 + 3) + 4 from by ring, pow_add]
    field_simp
  · simp only [if_pos h1, if_neg h0]
    rw [show 2 * g 0 + 7 = (2 * g 0 + 3) + 4 from by ring, pow_add]
    field_simp
  · simp only [if_neg h0, if_neg h1]
    rw [show 2 * g 0 + 2 * g 1 + 6 = (2 * g 0 + 2 * g 1 + 3) + 3 from by ring, pow_add]
    field_simp
