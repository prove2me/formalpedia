-- Prove2me | solution 1 for PGLQuotient.rk3Weight_succ_row
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:46:00.403861+00:00
-- url     : https://prove2.me/submissions/5bbb27f4-c39e-440a-8a56-f026207b75fc

-- Sol generated from Algebra/PGLQuotient/VertexVolumeRankThree.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
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











/-! ### Summing over the dominant sector -/






theorem solution(a b : ℕ) :
    rk3Weight q (a + 1) b =
      if b = 0 then (q ^ 5 * (q - 1) ^ 2 * (q ^ 2 - 1))⁻¹ * ((q ^ 2)⁻¹) ^ a
      else ((q ^ 7 * (q - 1) ^ 3)⁻¹ * ((q ^ 2)⁻¹) ^ a) * ((q ^ 2)⁻¹) ^ (b - 1) := by
  unfold rk3Weight
  rw [if_neg (by omega)]
  cases b with
  | zero =>
    rw [if_pos rfl, if_pos rfl]
    rw [show 2 * (a + 1) + 3 = 5 + 2 * a from by ring, pow_add, pow_mul, inv_pow, ← mul_inv]
    congr 1
    ring
  | succ b =>
    rw [if_neg (by omega), if_neg (by omega)]
    rw [show 2 * (a + 1) + 2 * (b + 1) + 3 = 7 + 2 * a + 2 * b from by ring,
      pow_add, pow_add, pow_mul, pow_mul, inv_pow, inv_pow, ← mul_inv, ← mul_inv]
    congr 1
    simp only [Nat.add_sub_cancel]
    ring
