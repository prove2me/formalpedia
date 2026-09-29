-- Prove2me | solution 1 for PGLQuotient.heightZeta_rank_two_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:34:40.33736+00:00
-- url     : https://prove2.me/submissions/684bad50-a450-4529-a2e2-4aa69b71b70a

-- Sol generated from Algebra/PGLQuotient/HeightZetaRankTwo.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightZetaRankTwo
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
theorem solution(hq : 1 < q) (M : ℝ) :
    ∃ s : ℝ, s < 2 ∧ M < heightZeta q 2 s := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  set K : ℝ := (q - 1) ^ 2 * q with hK
  have hKpos : 0 < K := by
    have : (0:ℝ) < q - 1 := by linarith
    positivity
  have hMpos : (0:ℝ) < |M| + 1 := by positivity
  set e : ℝ := min ((q - 1) / 2) (1 / (K * (|M| + 1))) with he
  have hepos : 0 < e := lt_min (by linarith) (by positivity)
  have he1 : e ≤ (q - 1) / 2 := min_le_left _ _
  have he2 : e ≤ 1 / (K * (|M| + 1)) := min_le_right _ _
  have hqe1 : 1 < q - e := by linarith
  have hqe0 : 0 < q - e := by linarith
  refine ⟨2 * Real.logb q (q - e), ?_, ?_⟩
  · have : Real.logb q (q - e) < Real.logb q q :=
      Real.logb_lt_logb hq hqe0 (by linarith)
    rw [Real.logb_self_eq_one hq] at this
    linarith
  · have hs2 : (2 * Real.logb q (q - e)) / 2 = Real.logb q (q - e) := by ring
    have hu : q ^ ((2 * Real.logb q (q - e)) / 2) = q - e := by
      rw [hs2]
      exact Real.rpow_logb hq0 (ne_of_gt hq) hqe0
    have hlt : 2 * Real.logb q (q - e) < 2 := by
      have : Real.logb q (q - e) < Real.logb q q :=
        Real.logb_lt_logb hq hqe0 (by linarith)
      rw [Real.logb_self_eq_one hq] at this
      linarith
    rw [heightZeta_rank_two hq hlt, hu, show q - (q - e) = e from by ring]
    have hApos : 0 < (q * (q - 1) * (q ^ 2 - 1))⁻¹ := by
      have h1 : (0:ℝ) < q - 1 := by linarith
      have h2 : (0:ℝ) < q ^ 2 - 1 := by nlinarith
      positivity
    have hKe : 0 < K * e := by positivity
    have hbound : M < (q - e) / (K * e) := by
      rw [lt_div_iff₀ hKe]
      have habs : M ≤ |M| := le_abs_self M
      have hprod : (K * e) * (|M| + 1) ≤ 1 := by
        rw [← le_div_iff₀ hMpos]
        calc K * e ≤ K * (1 / (K * (|M| + 1))) := by nlinarith
          _ = 1 / (|M| + 1) := by field_simp
      nlinarith
    have hrewrite : (q - e) / ((q - 1) ^ 2 * q * e) = (q - e) / (K * e) := by
      rw [hK]
    rw [hrewrite]
    linarith
