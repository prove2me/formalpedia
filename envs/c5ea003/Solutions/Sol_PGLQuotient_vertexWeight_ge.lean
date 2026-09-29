-- Prove2me | solution 1 for PGLQuotient.vertexWeight_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:32:20.260978+00:00
-- url     : https://prove2.me/submissions/052a1716-d366-4bd2-ab07-1e530a366f51

-- Sol generated from Algebra/PGLQuotient/VertexModel.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_inv_lt_one_of_one_lt
import Theorems.Thm_PGLQuotient_one_le_blockRank
import Theorems.Thm_PGLQuotient_one_sub_inv_pos
import Theorems.Thm_PGLQuotient_sum_lam_sub_eq_pairExp

/-!
# The standard arithmetic quotient of `PGL_d`: the vertex model

This file sets up an explicit combinatorial model for the vertex set of the standard
non-uniform arithmetic quotient of the affine Bruhat–Tits building of
`PGL_d (F_q((t^{-1})))` by `Γ = PGL_d(F_q[t])`.

By Soulé's theorem the quotient `Γ \ X` is (simplicially) a dominant sector: its vertices are
in bijection with dominant coweights `λ = (λ_0 ≥ λ_1 ≥ ⋯ ≥ λ_{d-1} = 0)`, and the stabiliser
of the vertex `λ` in `GL_d(F_q[t])` is the group of matrices `(a_{ij})` over `F_q[t]` with
`deg a_{ij} ≤ λ_i - λ_j`; equivalently, it is the automorphism group of the vector bundle
`⨁_i O(λ_i)` on `P^1`, i.e. the unit group of the algebra `End = ⨁_{i,j} H^0(O(λ_i - λ_j))`.
Its order is

`|Aut(λ)| = q^{dim End} * ∏_i (1 - q^{-r_i})`,

where `dim End = ∑_{i,j} max (0, λ_i - λ_j + 1)` and `r_i = #{ j ≤ i : λ_j = λ_i }` is the
position of `i` inside its block of equal entries (so that the second factor accounts for the
Levi `∏_b GL_{m_b}(F_q)` of the block composition).  With the Haar measure normalised so that
a maximal compact subgroup has volume `1`, the vertex `λ` carries the mass `1/|Aut(λ)|`
(`GL`-normalisation) resp. `(q-1)/|Aut(λ)|` (`PGL`-normalisation).

Vertices are parametrised here by their *gaps* `g_k = λ_k - λ_{k+1} ∈ ℕ`, `0 ≤ k ≤ d-2`, i.e.
by `Vertex d = Fin (d-1) → ℕ`.

The homothety-invariant normalised lattice-minima height is
`α(λ) = q^{λ_0 - (λ_0 + ⋯ + λ_{d-1})/d}`, which in gap coordinates reads
`log_q α = (∑_k (d-1-k) g_k)/d`.

## Main results of this file

* `sum_lam_sub_eq_pairExp` : the cut-set/double-counting identity
  `∑_{i,j} (λ_i - λ_j) = ∑_k (k+1)(d-1-k) g_k`;
* `vertexWeight_le`, `vertexWeight_ge` : sharp-order two-sided bounds
  `c₁ q^{-P(g)} ≤ 1/|Aut(λ)| ≤ c₂ q^{-P(g)}` with `P(g) = ∑_k (k+1)(d-1-k) g_k`.

These drive all the analytic results (integrability threshold, cusp tail, height zeta
function) in the companion files.
-/

open PGLQuotient

open Finset


variable {d : ℕ}












variable (g : Vertex d)







lemma endDim_le_pairExp : endDim g ≤ pairExp g + d * d := by
  rw [← sum_lam_sub_eq_pairExp]
  unfold endDim
  calc ∑ i ∈ range d, ∑ j ∈ range d, (lam g i + 1 - lam g j)
      ≤ ∑ i ∈ range d, ∑ j ∈ range d, ((lam g i - lam g j) + 1) := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        omega
    _ = (∑ i ∈ range d, ∑ j ∈ range d, (lam g i - lam g j)) + d * d := by
        simp [Finset.sum_add_distrib, Finset.sum_const]




variable {q : ℝ} (g : Vertex d)


lemma blockFactor_le_one (hq : 1 < q) (r : ℕ) : 1 - q⁻¹ ^ r ≤ 1 := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have : (0:ℝ) ≤ q⁻¹ ^ r := pow_nonneg (le_of_lt (inv_pos.mpr hq0)) r
  linarith

lemma blockFactor_ge (hq : 1 < q) {r : ℕ} (hr : 1 ≤ r) : 1 - q⁻¹ ≤ 1 - q⁻¹ ^ r := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have h1 : q⁻¹ ^ r ≤ q⁻¹ ^ 1 :=
    pow_le_pow_of_le_one (le_of_lt (inv_pos.mpr hq0)) (le_of_lt (inv_lt_one_of_one_lt hq)) hr
  simp only [pow_one] at h1
  linarith


lemma prod_blockFactor_le_one (hq : 1 < q) :
    ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) ≤ 1 := by
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => blockFactor_le_one hq _)
  have := blockFactor_ge (q := q) hq (one_le_blockRank g i)
  have := one_sub_inv_pos (q := q) hq
  linarith

lemma prod_blockFactor_ge (hq : 1 < q) :
    (1 - q⁻¹) ^ d ≤ ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) := by
  have h := one_sub_inv_pos (q := q) hq
  calc (1 - q⁻¹) ^ d = ∏ _i ∈ range d, (1 - q⁻¹) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) := by
        refine Finset.prod_le_prod (fun i _ => le_of_lt h)
          (fun i _ => blockFactor_ge hq (one_le_blockRank g i))

lemma prod_blockFactor_pos (hq : 1 < q) :
    0 < ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) :=
  lt_of_lt_of_le (pow_pos (one_sub_inv_pos hq) d) (prod_blockFactor_ge g hq)

lemma autOrder_pos (hq : 1 < q) : 0 < autOrder q g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  exact mul_pos (pow_pos hq0 _) (prod_blockFactor_pos g hq)






open PGLQuotient in
theorem solution(hq : 1 < q) :
    (q ^ (d * d))⁻¹ * (q ^ pairExp g)⁻¹ ≤ vertexWeight q g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hhigh : autOrder q g ≤ q ^ (pairExp g + d * d) := by
    unfold autOrder
    calc q ^ endDim g * ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i)
        ≤ q ^ endDim g * 1 := by
          exact mul_le_mul_of_nonneg_left (prod_blockFactor_le_one g hq)
            (le_of_lt (pow_pos hq0 _))
      _ = q ^ endDim g := by ring
      _ ≤ q ^ (pairExp g + d * d) := pow_le_pow_right₀ hq.le (endDim_le_pairExp g)
  unfold vertexWeight
  rw [show (q ^ (d * d))⁻¹ * (q ^ pairExp g)⁻¹ = (q ^ (pairExp g + d * d))⁻¹ by
    rw [pow_add, mul_inv]; ring]
  exact inv_anti₀ (autOrder_pos g hq) hhigh
