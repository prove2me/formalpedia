-- Prove2me | solution 1 for PGLQuotient.endDim_open
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:33:55.094742+00:00
-- url     : https://prove2.me/submissions/21dc51cb-47d6-4914-b43b-a2e2ee85682a

-- Sol generated from Algebra/PGLQuotient/OpenStratum.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_OpenStratum
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_lam_antitone
import Theorems.Thm_PGLQuotient_lam_lt_of_gap_pos
import Theorems.Thm_PGLQuotient_sum_lam_sub_eq_pairExp

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

lemma sum_range_sub_eq (n : ℕ) : ∑ i ∈ range n, (n - i) = n + n * (n - 1) / 2 := by
  have h1 : ∑ i ∈ range n, (n - i) = ∑ i ∈ range n, (i + 1) := by
    conv_rhs => rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have := Finset.mem_range.mp hi
    omega
  have h2 : ∑ i ∈ range n, (i + 1) = (∑ i ∈ range n, i) + n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have h3 := Finset.sum_range_id_mul_two n
  omega

/-! ### The open stratum -/


variable (g : Vertex d)






/-! ### The mass of the open stratum -/







open PGLQuotient in
theorem solution(h : ∀ k, 1 ≤ g k) :
    endDim g = pairExp g + (d + d * (d - 1) / 2) := by
  have hterm : ∀ i ∈ range d, ∀ j ∈ range d,
      (lam g i + 1 - lam g j) = (lam g i - lam g j) + (if i ≤ j then 1 else 0) := by
    intro i hi j hj
    have hi' := Finset.mem_range.mp hi
    by_cases hij : i ≤ j
    · have := lam_antitone g hij
      rw [if_pos hij]
      omega
    · have hji : j < i := by omega
      have := lam_lt_of_gap_pos g h hji hi'
      rw [if_neg hij]
      omega
  have hsplit : endDim g
      = (∑ i ∈ range d, ∑ j ∈ range d, (lam g i - lam g j))
        + ∑ i ∈ range d, ∑ j ∈ range d, (if i ≤ j then 1 else 0) := by
    unfold endDim
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j hj => hterm i hi j hj)
  have hcount : ∀ i ∈ range d, (∑ j ∈ range d, (if i ≤ j then 1 else 0)) = d - i := by
    intro i _
    rw [← Finset.sum_filter]
    have hf : (range d).filter (fun j => i ≤ j) = Finset.Ico i d := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hf, Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
  rw [hsplit, sum_lam_sub_eq_pairExp, Finset.sum_congr rfl hcount, sum_range_sub_eq]
