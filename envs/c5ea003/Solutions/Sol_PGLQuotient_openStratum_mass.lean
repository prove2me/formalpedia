-- Prove2me | solution 1 for PGLQuotient.openStratum_mass
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:45:59.681886+00:00
-- url     : https://prove2.me/submissions/ae0fdc44-ec9e-4fc2-a18f-035ca8558627

-- Sol generated from Algebra/PGLQuotient/OpenStratum.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_OpenStratum
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_blockRank_open
import Theorems.Thm_PGLQuotient_endDim_open
import Theorems.Thm_PGLQuotient_gapAt_coe
import Theorems.Thm_PGLQuotient_summable_pi_geom

/-!
# The open stratum of the dominant sector, in every rank

The dominant sector `ℕ^{d-1}` parametrising the vertices of the standard arithmetic quotient
is stratified by the vanishing pattern of the gaps `g_k = λ_k - λ_{k+1}`; this is the
"cut-set" decomposition used to evaluate the vertex volume.  Here we treat the *open* (generic)
stratum `g_k ≥ 1` for all `k`, in **arbitrary rank `d`**, and obtain its mass in closed
product form:

`∑_{λ regular dominant} 1/|Aut λ| = 1 / ( q^{d(d-1)/2} (q-1)^d ∏_{k=1}^{d-1} (q^{k(d-k)} - 1) )`.

For `d = 2` this is `1/(q (q-1)^3)` and for `d = 3` it is `1/(q^3 (q-1)^3 (q^2-1)^2)`,
matching the open-stratum terms of `vertexVolume_rank_two` and `vertexVolume_rank_three`.

The three building-theoretic inputs, all established here in arbitrary rank, are:

* `lam_lt_of_gap_pos`  : on the open stratum the coweight `λ` is strictly decreasing;
* `blockRank_open`     : hence every block has size one, so the reductive part of the
  stabiliser is a maximal torus and contributes `(1 - q^{-1})^d`;
* `endDim_open`        : hence `dim End(⨁ O(λ_i)) = ∑_{i<j}(λ_i - λ_j) + d(d+1)/2` exactly.

The resulting sum is a product of `d-1` independent geometric series, evaluated with
`summable_pi_geom`.
-/

open PGLQuotient

open Finset

variable {d : ℕ} {q : ℝ}

/-! ### A triangular-number identity -/


/-! ### The open stratum -/


variable (g : Vertex d)




/-- The exact stabiliser order on the open stratum, in arbitrary rank. -/
lemma autOrder_open (h : ∀ k, 1 ≤ g k) :
    autOrder q g = q ^ (pairExp g + (d + d * (d - 1) / 2)) * (1 - q⁻¹) ^ d := by
  unfold autOrder
  rw [endDim_open g h]
  congr 1
  rw [Finset.prod_congr rfl (fun i hi => by
      rw [blockRank_open g h (Finset.mem_range.mp hi)]), Finset.prod_const, Finset.card_range]
  simp


/-! ### The mass of the open stratum -/



lemma pairExp_shift (g : Vertex d) :
    pairExp (fun k => g k + 1) = pairExp g + pairSum d := by
  unfold pairExp pairSum pairCoef
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k < d - 1 := Finset.mem_range.mp hk
  rw [gapAt, dif_pos hk', gapAt, dif_pos hk']
  ring

lemma pairExp_eq_fin_sum (g : Vertex d) :
    pairExp g = ∑ k : Fin (d - 1), pairCoef d (k : ℕ) * g k := by
  have h1 : ∑ k : Fin (d - 1), pairCoef d (k : ℕ) * g k
      = ∑ k ∈ range (d - 1), pairCoef d k * gapAt g k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => pairCoef d k * gapAt g k) (d - 1)]
    exact Finset.sum_congr rfl (fun k _ => by rw [gapAt_coe])
  rw [h1]
  unfold pairExp pairCoef
  rfl



theorem solution(hq : 1 < q) :
    ∑' g : Vertex d, vertexWeight q (fun k => g k + 1)
      = (q ^ (d * (d - 1) / 2) * (q - 1) ^ d)⁻¹
        * ∏ k ∈ range (d - 1), (q ^ pairCoef d k - 1)⁻¹ := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hq1 : (0:ℝ) < q - 1 := by linarith
  have hq1' : q - 1 ≠ 0 := ne_of_gt hq1
  have hcpos : ∀ k : Fin (d - 1), 1 ≤ pairCoef d (k : ℕ) := by
    intro k
    have hk := k.isLt
    unfold pairCoef
    have h2 : 1 ≤ d - 1 - (k : ℕ) := by omega
    calc 1 = 1 * 1 := by ring
      _ ≤ ((k : ℕ) + 1) * (d - 1 - (k : ℕ)) := Nat.mul_le_mul (by omega) h2
  have hqcgt : ∀ k : Fin (d - 1), 1 < q ^ pairCoef d (k : ℕ) :=
    fun k => one_lt_pow₀ hq (by have := hcpos k; omega)
  have hx0 : ∀ k : Fin (d - 1), (0:ℝ) ≤ (q ^ pairCoef d (k : ℕ))⁻¹ := fun k => by positivity
  have hx1 : ∀ k : Fin (d - 1), (q ^ pairCoef d (k : ℕ))⁻¹ < 1 := by
    intro k
    rw [inv_lt_one_iff₀]
    right
    exact hqcgt k
  obtain ⟨hsum, hval⟩ :=
    summable_pi_geom (fun k : Fin (d - 1) => (q ^ pairCoef d (k : ℕ))⁻¹) hx0 hx1
  have hweight : ∀ g : Vertex d,
      vertexWeight q (fun k => g k + 1)
        = (q ^ (pairSum d + (d + d * (d - 1) / 2)) * (1 - q⁻¹) ^ d)⁻¹
          * ∏ k : Fin (d - 1), ((q ^ pairCoef d (k : ℕ))⁻¹) ^ g k := by
    intro g
    have hpos : ∀ k : Fin (d - 1), 1 ≤ (fun k => g k + 1) k := fun k => Nat.le_add_left 1 _
    have hprodx : ∏ k : Fin (d - 1), ((q ^ pairCoef d (k : ℕ))⁻¹) ^ g k = (q ^ pairExp g)⁻¹ := by
      simp only [← inv_pow, ← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum, ← pairExp_eq_fin_sum g]
    unfold vertexWeight
    rw [autOrder_open (q := q) (fun k => g k + 1) hpos, pairExp_shift g, hprodx,
      show pairExp g + pairSum d + (d + d * (d - 1) / 2)
        = (pairSum d + (d + d * (d - 1) / 2)) + pairExp g from by ring, pow_add]
    simp only [mul_inv]
    ring
  rw [tsum_congr hweight, hsum.tsum_mul_left, hval]
  have hfactor : ∀ k : Fin (d - 1),
      (1 - (q ^ pairCoef d (k : ℕ))⁻¹)⁻¹
        = q ^ pairCoef d (k : ℕ) * (q ^ pairCoef d (k : ℕ) - 1)⁻¹ := by
    intro k
    have h1 : (0:ℝ) < q ^ pairCoef d (k : ℕ) := by positivity
    have h2 : q ^ pairCoef d (k : ℕ) - 1 ≠ 0 := by have := hqcgt k; linarith
    have key : (1 : ℝ) - (q ^ pairCoef d (k : ℕ))⁻¹
        = (q ^ pairCoef d (k : ℕ) - 1) / q ^ pairCoef d (k : ℕ) := by
      field_simp
    rw [key, inv_div, div_eq_mul_inv]
  rw [Finset.prod_congr rfl (fun k _ => hfactor k), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hSfin : ∑ k : Fin (d - 1), pairCoef d (k : ℕ) = pairSum d :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => pairCoef d k) (d - 1)
  have hPfin : ∏ k : Fin (d - 1), (q ^ pairCoef d (k : ℕ) - 1)⁻¹
      = ∏ k ∈ range (d - 1), (q ^ pairCoef d k - 1)⁻¹ :=
    Fin.prod_univ_eq_prod_range (fun k : ℕ => (q ^ pairCoef d k - 1)⁻¹) (d - 1)
  rw [hSfin, hPfin]
  have hinvq : (1 : ℝ) - q⁻¹ = (q - 1) / q := by field_simp
  rw [hinvq, div_pow, pow_add, pow_add]
  have hqs : (q : ℝ) ^ pairSum d ≠ 0 := pow_ne_zero _ hqne
  have hqd : (q : ℝ) ^ d ≠ 0 := pow_ne_zero _ hqne
  have hqD : (q : ℝ) ^ (d * (d - 1) / 2) ≠ 0 := pow_ne_zero _ hqne
  field_simp
