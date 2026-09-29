-- Prove2me | Definitions.Def_Algebra_PGLQuotient_OpenStratum
-- name    : Algebra_PGLQuotient_OpenStratum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:33:22.954949+00:00
-- url     : https://prove2.me/theorems/e2620efa-a07b-4e92-8591-1543a1d1dedb
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_OpenStratum
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.OpenStratum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/OpenStratum.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_HeightThreshold

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

namespace PGLQuotient

open Finset

variable {d : ℕ} {q : ℝ}

/-! ### A triangular-number identity -/


/-! ### The open stratum -/

section OpenStratum

variable (g : Vertex d)





end OpenStratum

/-! ### The mass of the open stratum -/

/-- The coefficient of `g_k` in `∑_{i<j} (λ_i - λ_j)`, namely `(k+1)(d-1-k)`. -/
def pairCoef (d k : ℕ) : ℕ := (k + 1) * (d - 1 - k)

/-- The total coefficient `∑_{k=1}^{d-1} k(d-k)`. -/
def pairSum (d : ℕ) : ℕ := ∑ k ∈ range (d - 1), pairCoef d k




end PGLQuotient


