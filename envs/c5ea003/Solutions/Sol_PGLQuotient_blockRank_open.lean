-- Prove2me | solution 1 for PGLQuotient.blockRank_open
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:22:23.51101+00:00
-- url     : https://prove2.me/submissions/77f55e52-6145-4061-a20a-de97baf666fc

-- Sol generated from Algebra/PGLQuotient/OpenStratum.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_OpenStratum
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_lam_lt_of_gap_pos

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






/-! ### The mass of the open stratum -/







open PGLQuotient in
theorem solution(h : ∀ k, 1 ≤ g k) {i : ℕ} (hi : i < d) : blockRank g i = 1 := by
  have hfil : (range (i + 1)).filter (fun j => lam g j = lam g i) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hlam⟩
      by_contra hne
      have hji : j < i := by omega
      exact absurd hlam (ne_of_gt (lam_lt_of_gap_pos g h hji hi))
    · rintro rfl
      exact ⟨Nat.lt_succ_self _, rfl⟩
  unfold blockRank
  rw [hfil, Finset.card_singleton]
