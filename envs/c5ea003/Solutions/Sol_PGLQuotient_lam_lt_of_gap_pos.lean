-- Prove2me | solution 1 for PGLQuotient.lam_lt_of_gap_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:20:53.042955+00:00
-- url     : https://prove2.me/submissions/f18a740a-8d83-43a7-80e6-f940d55513a3

-- Sol generated from Algebra/PGLQuotient/OpenStratum.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_OpenStratum
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_lam_antitone
import Theorems.Thm_PGLQuotient_lam_sub

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
theorem solution(h : ∀ k, 1 ≤ g k) {i j : ℕ} (hji : j < i) (hi : i < d) :
    lam g i < lam g j := by
  have hid : i ≤ d - 1 := by omega
  have hsub : lam g j - lam g i = ∑ k ∈ Finset.Ico j i, gapAt g k :=
    lam_sub g hji.le hid
  have hpos : 1 ≤ ∑ k ∈ Finset.Ico j i, gapAt g k := by
    have hmem : j ∈ Finset.Ico j i := Finset.mem_Ico.mpr ⟨le_refl _, hji⟩
    have hterm : 1 ≤ gapAt g j := by
      have hjd : j < d - 1 := by omega
      rw [gapAt, dif_pos hjd]
      exact h _
    calc 1 ≤ gapAt g j := hterm
      _ ≤ ∑ k ∈ Finset.Ico j i, gapAt g k :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hmem
  have hanti : lam g i ≤ lam g j := lam_antitone g hji.le
  omega
