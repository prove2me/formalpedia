-- Prove2me | solution 1 for PGLQuotient.heightZeta_rank_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:32:31.303478+00:00
-- url     : https://prove2.me/submissions/b92062da-b791-40e3-9795-22776d6cfed9

-- Sol generated from Algebra/PGLQuotient/HeightZetaRankTwo.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_autOrder_rank_two
import Theorems.Thm_PGLQuotient_height_pow
import Theorems.Thm_PGLQuotient_summable_weight_height_of_lt

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



lemma heightExp_rank_two (g : Vertex 2) : heightExp g = g 0 := by
  simp [heightExp, gapAt]





lemma vertexWeight_rank_two (hq : 1 < q) (g : Vertex 2) :
    vertexWeight q g = if g 0 = 0 then (q * (q - 1) * (q ^ 2 - 1))⁻¹
      else ((q - 1) ^ 2 * q ^ (g 0 + 1))⁻¹ := by
  unfold vertexWeight
  rw [autOrder_rank_two hq]
  split <;> rfl

/-! ### The height zeta function in rank two -/








open PGLQuotient in
theorem solution(hq : 1 < q) {s : ℝ} (hs : s < 2) :
    heightZeta q 2 s
      = (q * (q - 1) * (q ^ 2 - 1))⁻¹ + q ^ (s / 2) / ((q - 1) ^ 2 * q * (q - q ^ (s / 2))) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hu0 : 0 < q ^ (s / 2) := Real.rpow_pos_of_pos hq0 _
  have huq : q ^ (s / 2) < q := by
    have h1 : s / 2 < 1 := by linarith
    calc q ^ (s / 2) < q ^ (1:ℝ) := (Real.rpow_lt_rpow_left_iff hq).mpr h1
      _ = q := Real.rpow_one q
  have hqu : 0 < q - q ^ (s / 2) := by linarith
  have hterm : ∀ g : Vertex 2, vertexWeight q g * height q g ^ s
      = (if g 0 = 0 then (q * (q - 1) * (q ^ 2 - 1))⁻¹
          else ((q - 1) ^ 2 * q ^ (g 0 + 1))⁻¹) * (q ^ (s / 2)) ^ (g 0) := by
    intro g
    rw [vertexWeight_rank_two hq g, height_pow hq g s, heightExp_rank_two]
    norm_num
  have hsummable : Summable (fun g : Vertex 2 => vertexWeight q g * height q g ^ s) :=
    summable_weight_height_of_lt hq (by norm_num) (by simpa using hs)
  have hreindex : heightZeta q 2 s
      = ∑' n : ℕ, (if n = 0 then (q * (q - 1) * (q ^ 2 - 1))⁻¹
          else ((q - 1) ^ 2 * q ^ (n + 1))⁻¹) * (q ^ (s / 2)) ^ n := by
    unfold heightZeta
    rw [tsum_congr hterm]
    exact ((Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq
      (fun g : Vertex 2 => (if g 0 = 0 then (q * (q - 1) * (q ^ 2 - 1))⁻¹
        else ((q - 1) ^ 2 * q ^ (g 0 + 1))⁻¹) * (q ^ (s / 2)) ^ (g 0))).symm
  have hsummableN : Summable (fun n : ℕ => (if n = 0 then (q * (q - 1) * (q ^ 2 - 1))⁻¹
      else ((q - 1) ^ 2 * q ^ (n + 1))⁻¹) * (q ^ (s / 2)) ^ n) := by
    have hcomp := hsummable.comp_injective
      (i := fun n : ℕ => ((Equiv.funUnique (Fin 1) ℕ).symm n : Vertex 2))
      (Equiv.injective _)
    refine hcomp.congr (fun n => ?_)
    simp only [Function.comp_apply]
    rw [hterm]
    rfl
  rw [hreindex, hsummableN.tsum_eq_zero_add]
  have hzero : (if (0:ℕ) = 0 then (q * (q - 1) * (q ^ 2 - 1))⁻¹
      else ((q - 1) ^ 2 * q ^ ((0:ℕ) + 1))⁻¹) * (q ^ (s / 2)) ^ (0:ℕ)
      = (q * (q - 1) * (q ^ 2 - 1))⁻¹ := by simp
  rw [hzero]
  congr 1
  have htail : ∀ n : ℕ, (if n + 1 = 0 then (q * (q - 1) * (q ^ 2 - 1))⁻¹
      else ((q - 1) ^ 2 * q ^ ((n + 1) + 1))⁻¹) * (q ^ (s / 2)) ^ (n + 1)
      = ((q ^ (s / 2)) * ((q - 1) ^ 2 * q ^ 2)⁻¹) * ((q ^ (s / 2)) / q) ^ n := by
    intro n
    rw [if_neg (by omega), div_pow, pow_succ, pow_add, pow_add]
    field_simp
    ring
  rw [tsum_congr htail]
  have hratio : (0:ℝ) ≤ (q ^ (s / 2)) / q := le_of_lt (div_pos hu0 hq0)
  have hratio1 : (q ^ (s / 2)) / q < 1 := by rw [div_lt_one hq0]; exact huq
  rw [(summable_geometric_of_lt_one hratio hratio1).tsum_mul_left,
    tsum_geometric_of_lt_one hratio hratio1]
  have hne : (1 : ℝ) - (q ^ (s / 2)) / q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by
    have : (0:ℝ) < q - 1 := by linarith
    exact ne_of_gt this
  field_simp
