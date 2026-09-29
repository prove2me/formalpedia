-- Prove2me | solution 1 for PGLQuotient.cuspTail_upper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:31:37.408383+00:00
-- url     : https://prove2.me/submissions/9d83cd34-818b-4f4d-9c77-4d71c7f49922

-- Sol generated from Algebra/PGLQuotient/CuspTail.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_height_gt_iff
import Theorems.Thm_PGLQuotient_inv_lt_one_of_one_lt
import Theorems.Thm_PGLQuotient_one_sub_inv_pos
import Theorems.Thm_PGLQuotient_resBase_lt_one
import Theorems.Thm_PGLQuotient_summable_pi_geom
import Theorems.Thm_PGLQuotient_summable_vertexWeight
import Theorems.Thm_PGLQuotient_tailMass_le
import Theorems.Thm_PGLQuotient_vertexWeight_pos

/-!
# The sharp cusp-tail estimate of order `T^{-d}`

For the standard arithmetic quotient of the Bruhat–Tits building of `PGL_d(F_q((t^{-1})))`,
with the normalised lattice-minima height `α` of `Algebra.PGLQuotient.VertexModel`, we prove
the two-sided cusp-tail estimate

`c · T^{-d} ≤ mass {α > T} ≤ C · T^{-d}`   for all `T ≥ 1`.

The upper bound is the delicate half: the naive estimate coming from the integrability
threshold only gives `T^{-r}` for every `r < d`.  The sharp exponent is obtained by
*fibering the gap lattice over the height exponent*: the linear form
`N(g) = ∑_k (d-1-k) g_k = d log_q α` determines the first gap coordinate `g_0` once the
remaining coordinates are known, and the residual exponent `R(g) = ∑_k k(d-1-k) g_k` does not
involve `g_0` at all.  Hence `∑_{N(g) = n} q^{-R(g)}` is bounded uniformly in `n`, and
summing the resulting geometric series in `n` produces the exact exponent `T^{-d}`.

The lower bound comes from a single vertex on the cusp ray `λ = (n, 0, …, 0)`.
-/

open PGLQuotient

open Finset

variable {d : ℕ} {q : ℝ}



/-! ### The fibering majorant -/


lemma resBase_nonneg (hq : 1 < q) (k : Fin (d - 1)) : 0 ≤ resBase q d k := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  unfold resBase
  split
  · exact le_rfl
  · positivity



/-- Summability of the fibering majorant on `ℕ × Vertex d`. -/
lemma summable_tailMajorant (hq : 1 < q) :
    Summable (fun p : ℕ × Vertex d => (q⁻¹) ^ p.1 * ∏ k, resBase q d k ^ (p.2 k)) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hinv : q⁻¹ < 1 := inv_lt_one_of_one_lt hq
  have hinv0 : (0:ℝ) ≤ q⁻¹ := le_of_lt (inv_pos.mpr hq0)
  obtain ⟨hs2, -⟩ := summable_pi_geom (resBase q d) (resBase_nonneg hq) (resBase_lt_one hq)
  have hsum1 : Summable (fun n : ℕ => (q⁻¹) ^ n) := summable_geometric_of_lt_one hinv0 hinv
  have hnn1 : (0 : ℕ → ℝ) ≤ fun n : ℕ => (q⁻¹) ^ n := fun n => pow_nonneg hinv0 n
  have hnn2 : (0 : Vertex d → ℝ) ≤ fun h : Vertex d => ∏ k, resBase q d k ^ h k :=
    fun h => Finset.prod_nonneg (fun k _ => pow_nonneg (resBase_nonneg hq k) _)
  exact (hsum1.mul_of_nonneg hs2 hnn1 hnn2).congr (fun p => rfl)




/-! ### From the fibered bound to the sharp `T^{-d}` cusp tail -/






open PGLQuotient in
theorem solution(hq : 1 < q) (hd : 2 ≤ d) :
    ∃ C > 0, ∀ T : ℝ, 1 ≤ T → cuspTail q d T ≤ C * T ^ (-(d:ℝ)) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hpos1 : (0:ℝ) < ((1 - q⁻¹) ^ d)⁻¹ := by
    have := one_sub_inv_pos (q := q) hq
    positivity
  have hmaj := summable_tailMajorant (q := q) (d := d) hq
  set S : ℝ := ∑' p : ℕ × Vertex d, (q⁻¹) ^ p.1 * ∏ k, resBase q d k ^ (p.2 k) with hS
  have hnn : ∀ p : ℕ × Vertex d, 0 ≤ (q⁻¹) ^ p.1 * ∏ k, resBase q d k ^ (p.2 k) := by
    intro p
    exact mul_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hq0)) _)
      (Finset.prod_nonneg (fun k _ => pow_nonneg (resBase_nonneg hq k) _))
  have hSpos : 0 < S := by
    have hterm : (0:ℝ) < (q⁻¹) ^ (0:ℕ) * ∏ k, resBase q d k ^ ((0 : Vertex d) k) := by
      simp
    calc (0:ℝ) < (q⁻¹) ^ (0:ℕ) * ∏ k, resBase q d k ^ ((0 : Vertex d) k) := hterm
      _ ≤ S := hmaj.le_tsum ((0 : ℕ), (0 : Vertex d)) (fun j _ => hnn j)
  refine ⟨((1 - q⁻¹) ^ d)⁻¹ * S, by positivity, ?_⟩
  intro T hT
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  set L : ℝ := Real.logb q T with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg hq hT
  have hTq : q ^ L = T := Real.rpow_logb hq0 (ne_of_gt hq) hT0
  set n₀ : ℕ := ⌊(d : ℝ) * L⌋₊ with hn₀
  have hdL0 : (0:ℝ) ≤ (d : ℝ) * L := by positivity
  have hsub : ∀ g : Vertex d, T < height q g → n₀ < heightExp g := by
    intro g hg
    have h1 : (d : ℝ) * L < heightExp g := (height_gt_iff hq hd hT g).mp hg
    have h2 : ((n₀ : ℕ) : ℝ) ≤ (d : ℝ) * L := Nat.floor_le hdL0
    exact_mod_cast lt_of_le_of_lt h2 h1
  have hsum0 := summable_vertexWeight (q := q) (d := d) hq hd
  have hsub1 : Summable (fun g : {g : Vertex d | T < height q g} =>
      vertexWeight q (g : Vertex d)) := hsum0.subtype _
  have hsub2 : Summable (fun g : {g : Vertex d | n₀ < heightExp g} =>
      vertexWeight q (g : Vertex d)) := hsum0.subtype _
  have hmono : cuspTail q d T
      ≤ ∑' g : {g : Vertex d | n₀ < heightExp g}, vertexWeight q (g : Vertex d) := by
    refine Summable.tsum_le_tsum_of_inj
      (fun g : {g : Vertex d | T < height q g} =>
        (⟨(g : Vertex d), hsub _ g.2⟩ : {g : Vertex d | n₀ < heightExp g}))
      ?_ (fun c _ => le_of_lt (vertexWeight_pos _ hq)) (fun g => le_rfl) hsub1 hsub2
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  have hkey := tailMass_le (q := q) (d := d) hq hd n₀
  have hqT : T ^ (d:ℝ) ≤ q ^ (n₀ + 1) := by
    have h1 : (d : ℝ) * L < ((n₀ + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one _
    have h2 : T ^ (d:ℝ) = q ^ ((d : ℝ) * L) := by
      rw [← hTq, ← Real.rpow_mul (le_of_lt hq0)]
      ring_nf
    rw [h2, ← Real.rpow_natCast q (n₀ + 1)]
    exact le_of_lt ((Real.rpow_lt_rpow_left_iff hq).mpr h1)
  have hinv : (q ^ (n₀ + 1))⁻¹ ≤ T ^ (-(d:ℝ)) := by
    have hTd : (0:ℝ) < T ^ (d:ℝ) := Real.rpow_pos_of_pos hT0 _
    rw [Real.rpow_neg (le_of_lt hT0)]
    exact inv_anti₀ hTd hqT
  calc cuspTail q d T ≤ ∑' g : {g : Vertex d | n₀ < heightExp g}, vertexWeight q (g : Vertex d) :=
        hmono
    _ ≤ (((1 - q⁻¹) ^ d)⁻¹ * (q ^ (n₀ + 1))⁻¹) * S := hkey
    _ ≤ (((1 - q⁻¹) ^ d)⁻¹ * T ^ (-(d:ℝ))) * S := by
        refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hSpos)
        exact mul_le_mul_of_nonneg_left hinv (le_of_lt hpos1)
    _ = ((1 - q⁻¹) ^ d)⁻¹ * S * T ^ (-(d:ℝ)) := by ring
