-- Prove2me | solution 1 for PGLQuotient.summable_twZ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:40:54.763518+00:00
-- url     : https://prove2.me/submissions/8cd1e5d0-612e-44fa-ab9b-72b06975ada2

-- Sol generated from Algebra/PGLQuotient/HeightZetaGeneral.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightZetaGeneral
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_prod_gapRatioW
import Theorems.Thm_PGLQuotient_summable_pi_geom
import Theorems.Thm_PGLQuotient_twWeight_le_vertexWeight
import Theorems.Thm_PGLQuotient_twWeight_pos
import Theorems.Thm_PGLQuotient_vertexWeight_le

/-!
# The height zeta function in arbitrary rank: rationality and the pole at `s = d`

`Algebra.PGLQuotient.HeightZetaRankTwo` computes the positive-moment height zeta function

`Z_d(s) = ∑_λ α(λ)^s / |Aut λ|`

of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))` in closed form for `d = 2`,
exhibiting it as a rational function of `u = q^{s/2}` with a single pole at `u = q`.
This file establishes the corresponding statement in **arbitrary rank `d ≥ 1`**.

The mechanism is the same row-peeling recursion that produced the vertex volume in
`Algebra.PGLQuotient.VertexVolumeGeneral`, run on a *height-weighted* twisted mass

`twZ q c j w λ = w ^ heightExp λ · twWeight q c j λ`.

Since `heightExp (cons a λ') = (n+1)·a + heightExp λ'`, the extra factor is compatible with
peeling: it only changes the ratio of the geometric series in the top gap from
`q^{-(n+1)(c+1)}` to `w^{n+1} q^{-(n+1)(c+1)}`.  Hence:

* `twZMass_succ` — the row-peeling recursion for the height-weighted twisted mass;
* `twZ_rational` — for every rank and every pair of twisting parameters the sum is a rational
  function of `w` on the whole interval `0 ≤ w < q`, with a denominator that does not vanish
  there;
* `heightZeta_rational_general` — **the height zeta function of the rank-`d` quotient is a
  rational function of `u = q^{s/d}`**, uniformly for `s < d`;
* `heightZeta_unbounded_general` — **the pole at `s = d` is genuine in every rank**:
  `Z_d(s) → ∞` as `s ↑ d`.  Combined with `summable_weight_height_iff` this pins the abscissa
  of convergence at exactly `s = d`.

The threshold `w < q` is exactly `s < d` under `w = q^{s/d}`, so the domain of rationality is
precisely the half-plane of convergence.
-/

open PGLQuotient

open Finset

variable {q : ℝ}




variable {d : ℕ}


lemma gapRatioW_nonneg (hq : 1 < q) {w : ℝ} (hw : 0 ≤ w) (k : Fin (d - 1)) :
    0 ≤ gapRatioW q d w k := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  unfold gapRatioW
  positivity

lemma gapRatioW_lt_one (hq : 1 < q) {w : ℝ} (hw : 0 ≤ w) (hwq : w < q) (k : Fin (d - 1)) :
    gapRatioW q d w k < 1 := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  set m : ℕ := d - 1 - (k : ℕ) with hm
  have hm1 : 1 ≤ m := by have := k.isLt; omega
  have h1 : w ^ m < q ^ m := pow_lt_pow_left₀ hwq hw (by omega)
  have h2 : q ^ m ≤ q ^ (((k : ℕ) + 1) * m) :=
    pow_le_pow_right₀ hq.le (Nat.le_mul_of_pos_left m (Nat.succ_pos (k : ℕ)))
  unfold gapRatioW
  rw [← hm, inv_mul_lt_one₀ (pow_pos hq0 _)]
  exact lt_of_lt_of_le h1 h2




variable {w : ℝ}







open Polynomial








open PGLQuotient in
theorem solution(hq : 1 < q) (hw : 0 ≤ w) (hwq : w < q) (n c j : ℕ) :
    Summable (fun g : Vertex (n + 1) => twZ q c j w g) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  obtain ⟨hsum, -⟩ := summable_pi_geom (gapRatioW q (n + 1) w)
    (gapRatioW_nonneg hq hw) (gapRatioW_lt_one hq hw hwq)
  refine Summable.of_nonneg_of_le (fun g => ?_) (fun g => ?_)
    (hsum.mul_left (((1 - q⁻¹) ^ (n + 1))⁻¹))
  · exact mul_nonneg (pow_nonneg hw _) (twWeight_pos hq c j g).le
  · rw [prod_gapRatioW w g, ← mul_assoc]
    have hle : twWeight q c j g ≤ ((1 - q⁻¹) ^ (n + 1))⁻¹ * (q ^ pairExp g)⁻¹ :=
      le_trans (twWeight_le_vertexWeight hq c j g) (vertexWeight_le g hq)
    calc w ^ heightExp g * twWeight q c j g
        ≤ w ^ heightExp g * (((1 - q⁻¹) ^ (n + 1))⁻¹ * (q ^ pairExp g)⁻¹) :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg hw _)
      _ = ((1 - q⁻¹) ^ (n + 1))⁻¹ * (q ^ pairExp g)⁻¹ * w ^ heightExp g := by ring
