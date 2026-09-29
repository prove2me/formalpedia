-- Prove2me | solution 1 for PGLQuotient.twWeight_le_vertexWeight
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:34:07.021729+00:00
-- url     : https://prove2.me/submissions/988bea77-bf4c-4fd0-9ee3-f543e913d8f5

-- Sol generated from Algebra/PGLQuotient/TwistedWeight.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_inv_lt_one_of_one_lt
import Theorems.Thm_PGLQuotient_one_le_blockRank

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

lemma blockProdShift_zero (g : Vertex d) :
    blockProdShift q 0 g = ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) := by
  unfold blockProdShift
  exact Finset.prod_congr rfl (fun i _ => by simp)


/-- Every Levi factor `1 - q^{-r}` with `r ≥ 1` is positive. -/
lemma one_sub_inv_pow_pos (hq : 1 < q) {r : ℕ} (hr : 1 ≤ r) : 0 < 1 - q⁻¹ ^ r := by
  have h1 : q⁻¹ ^ r ≤ q⁻¹ ^ 1 :=
    pow_le_pow_of_le_one (le_of_lt (inv_pos.mpr (lt_trans zero_lt_one hq)))
      (le_of_lt (inv_lt_one_of_one_lt hq)) hr
  have h2 : q⁻¹ < 1 := inv_lt_one_of_one_lt hq
  simp only [pow_one] at h1
  linarith

/-- The Levi factors increase with the shift. -/
lemma one_sub_inv_pow_mono (hq : 1 < q) {r s : ℕ} (hrs : r ≤ s) :
    1 - q⁻¹ ^ r ≤ 1 - q⁻¹ ^ s := by
  have h1 : q⁻¹ ^ s ≤ q⁻¹ ^ r :=
    pow_le_pow_of_le_one (le_of_lt (inv_pos.mpr (lt_trans zero_lt_one hq)))
      (le_of_lt (inv_lt_one_of_one_lt hq)) hrs
  linarith

lemma blockProdShift_pos (hq : 1 < q) (j : ℕ) (g : Vertex d) : 0 < blockProdShift q j g :=
  Finset.prod_pos (fun i _ => one_sub_inv_pow_pos hq (by have := one_le_blockRank g i; omega))





variable {n : ℕ}














variable {q : ℝ}





open PGLQuotient in
theorem solution(hq : 1 < q) (c j : ℕ) (g : Vertex d) :
    twWeight q c j g ≤ vertexWeight q g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hvw : vertexWeight q g = (q ^ endDim g * blockProdShift q 0 g)⁻¹ := by
    rw [blockProdShift_zero]
    rfl
  have h0 : 0 < q ^ endDim g * blockProdShift q 0 g :=
    mul_pos (pow_pos hq0 _) (blockProdShift_pos hq 0 g)
  have hBP : blockProdShift q 0 g ≤ blockProdShift q j g := by
    unfold blockProdShift
    refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
    · exact le_of_lt (one_sub_inv_pow_pos hq
        (by have := one_le_blockRank g i; split_ifs <;> omega))
    · exact one_sub_inv_pow_mono hq (by split_ifs <;> omega)
  have hle : q ^ endDim g * blockProdShift q 0 g
      ≤ q ^ (endDim g + c * sigmaExp g + j * firstBlockSize g) * blockProdShift q j g :=
    mul_le_mul (pow_le_pow_right₀ hq.le (by omega)) hBP
      (le_of_lt (blockProdShift_pos hq 0 g)) (le_of_lt (pow_pos hq0 _))
  rw [hvw]
  exact inv_anti₀ h0 hle
