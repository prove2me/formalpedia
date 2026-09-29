-- Prove2me | Theorems.Thm_PGLQuotient_openStratum_mass
-- name    : PGLQuotient.openStratum_mass
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:48:51.135531+00:00
-- url     : https://prove2.me/theorems/e883c7ef-3dc5-4a4e-8a57-037e378049ac
-- title:
--   The mass of the open stratum, in arbitrary rank.
-- statement:
--   **The mass of the open stratum, in arbitrary rank.**  Summing `1/|Aut λ|` over the regular
--   dominant coweights (all gaps `≥ 1`) gives the closed product form
--   `1 / (q^{d(d-1)/2} (q-1)^d ∏_{k=1}^{d-1} (q^{k(d-k)} - 1))`.
--
--   ```lean
--   theorem PGLQuotient.openStratum_mass(hq : 1 < q) :
--       ∑' g : Vertex d, vertexWeight q (fun k => g k + 1)
--         = (q ^ (d * (d - 1) / 2) * (q - 1) ^ d)⁻¹
--           * ∏ k ∈ range (d - 1), (q ^ pairCoef d k - 1)⁻¹ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/OpenStratum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/OpenStratum.lean#L158

-- Thm stub generated from Algebra/PGLQuotient/OpenStratum.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold
import Definitions.Def_Algebra_PGLQuotient_OpenStratum
import Definitions.Def_Algebra_PGLQuotient_VertexModel

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

theorem PGLQuotient.openStratum_mass(hq : 1 < q) :
    ∑' g : Vertex d, vertexWeight q (fun k => g k + 1)
      = (q ^ (d * (d - 1) / 2) * (q - 1) ^ d)⁻¹
        * ∏ k ∈ range (d - 1), (q ^ pairCoef d k - 1)⁻¹ := by sorry
