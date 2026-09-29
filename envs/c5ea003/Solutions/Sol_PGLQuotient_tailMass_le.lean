-- Prove2me | solution 1 for PGLQuotient.tailMass_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:29:49.767005+00:00
-- url     : https://prove2.me/submissions/cd36f6b8-d041-435b-b9c2-e1d28107acff

-- Sol generated from Algebra/PGLQuotient/CuspTail.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_CuspTail
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_inv_lt_one_of_one_lt
import Theorems.Thm_PGLQuotient_one_sub_inv_pos
import Theorems.Thm_PGLQuotient_pairExp_eq
import Theorems.Thm_PGLQuotient_prod_resBase
import Theorems.Thm_PGLQuotient_resBase_lt_one
import Theorems.Thm_PGLQuotient_summable_pi_geom
import Theorems.Thm_PGLQuotient_summable_vertexWeight
import Theorems.Thm_PGLQuotient_tailInjection_injective
import Theorems.Thm_PGLQuotient_vertexWeight_le

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
theorem solution(hq : 1 < q) (hd : 2 ≤ d) (n₀ : ℕ) :
    ∑' g : {g : Vertex d | n₀ < heightExp g}, vertexWeight q (g : Vertex d)
      ≤ (((1 - q⁻¹) ^ d)⁻¹ * (q ^ (n₀ + 1))⁻¹)
        * ∑' p : ℕ × Vertex d, (q⁻¹) ^ p.1 * ∏ k, resBase q d k ^ (p.2 k) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have h0 : 0 < d - 1 := by omega
  have hmaj := summable_tailMajorant (q := q) (d := d) hq
  have hsubsum : Summable (fun g : {g : Vertex d | n₀ < heightExp g} =>
      vertexWeight q (g : Vertex d)) := (summable_vertexWeight hq hd).subtype _
  have hcst : (0:ℝ) ≤ ((1 - q⁻¹) ^ d)⁻¹ * (q ^ (n₀ + 1))⁻¹ := by
    have := one_sub_inv_pos (q := q) hq
    positivity
  rw [← hmaj.tsum_mul_left]
  refine Summable.tsum_le_tsum_of_inj
    (fun g : {g : Vertex d | n₀ < heightExp g} =>
      ((heightExp (g : Vertex d) - (n₀ + 1) : ℕ),
        Function.update (g : Vertex d) ⟨0, h0⟩ 0))
    (tailInjection_injective n₀ h0) (fun p _ => ?_) (fun g => ?_) hsubsum
    (hmaj.mul_left _)
  · refine mul_nonneg hcst (mul_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hq0)) _) ?_)
    exact Finset.prod_nonneg (fun k _ => pow_nonneg (resBase_nonneg hq k) _)
  · -- the pointwise bound
    obtain ⟨g, hg⟩ := g
    simp only [Set.mem_setOf_eq] at hg
    rw [prod_resBase hq g h0]
    have hq' : (q:ℝ) ≠ 0 := ne_of_gt hq0
    have hres : (q⁻¹) ^ (heightExp g - (n₀ + 1)) * (q ^ resExp g)⁻¹
        = (q ^ (n₀ + 1)) * (q ^ pairExp g)⁻¹ := by
      obtain ⟨a, ha⟩ : ∃ a, heightExp g = a + (n₀ + 1) := ⟨heightExp g - (n₀ + 1), by omega⟩
      rw [pairExp_eq, ha, Nat.add_sub_cancel, inv_pow, pow_add, pow_add]
      field_simp
      ring
    calc vertexWeight q g ≤ ((1 - q⁻¹) ^ d)⁻¹ * (q ^ pairExp g)⁻¹ := vertexWeight_le g hq
      _ = ((1 - q⁻¹) ^ d)⁻¹ * (q ^ (n₀ + 1))⁻¹
            * ((q⁻¹) ^ (heightExp g - (n₀ + 1)) * (q ^ resExp g)⁻¹) := by
          rw [hres]
          field_simp
