-- Prove2me | solution 1 for PGLQuotient.vertexWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:29:39.000361+00:00
-- url     : https://prove2.me/submissions/6299d4ab-0bbd-46ea-bc6d-ba9e3a5d5af3

-- Sol generated from Algebra/PGLQuotient/VertexModel.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_inv_lt_one_of_one_lt
import Theorems.Thm_PGLQuotient_one_le_blockRank
import Theorems.Thm_PGLQuotient_one_sub_inv_pos

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











variable {q : ℝ} (g : Vertex d)



lemma blockFactor_ge (hq : 1 < q) {r : ℕ} (hr : 1 ≤ r) : 1 - q⁻¹ ≤ 1 - q⁻¹ ^ r := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have h1 : q⁻¹ ^ r ≤ q⁻¹ ^ 1 :=
    pow_le_pow_of_le_one (le_of_lt (inv_pos.mpr hq0)) (le_of_lt (inv_lt_one_of_one_lt hq)) hr
  simp only [pow_one] at h1
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
theorem solution(hq : 1 < q) : 0 < vertexWeight q g :=
  inv_pos.mpr (autOrder_pos g hq)
