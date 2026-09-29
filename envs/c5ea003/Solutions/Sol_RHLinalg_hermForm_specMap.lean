-- Prove2me | solution 1 for RHLinalg.hermForm_specMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:50:13.37885+00:00
-- url     : https://prove2.me/submissions/07f49c75-8b11-4c35-9afb-31b8745213b7

import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex

-- from Zeta23.LinAlg.HermitianPosPart
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Positive and negative parts of a Hermitian matrix

For a Hermitian matrix `Q` with spectral decomposition `Q = U diag(λ) Uᴴ`,
define `Q₊ := U diag(λ⁺) Uᴴ` and `Q₋ := U diag(λ⁻) Uᴴ` where
`λ⁺ = max(λ,0)`, `λ⁻ = max(−λ,0)`.

Then `Q = Q₊ − Q₋`, both are PSD, `Q₊ Q₋ = 0`, and `rank Q₊ = n₊(Q)`.

This is equivalent to the CFC `Q⁺`/`Q⁻` via `Matrix.IsHermitian.cfc_eq`, but
the direct spectral construction keeps the eigenvalue bookkeeping explicit,
which is what the rank–trace proof needs.
-/

noncomputable section

open Matrix Finset Unitary
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]












section PosNegPart

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)















end PosNegPart

end RHLinalg
end
open Matrix Finset Unitary
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ (specMap hA f *ᵥ x))
      = ∑ i, f (hA.eigenvalues i) *
          ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary
  set c := star U *ᵥ x with hc_def
  -- `xᴴ U D Uᴴ x = cᴴ D c` where `c = Uᴴ x`, since `star x ᵥ* U = star c`.
  have hsc : star x ᵥ* U = star c := by
    rw [hc_def, star_mulVec, show (star U)ᴴ = U from conjTranspose_conjTranspose U]
  unfold specMap
  rw [conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec (star x) U, hsc, ← hc_def,
    show star c ⬝ᵥ (diagonal (fun i => (f (hA.eigenvalues i) : 𝕜)) *ᵥ c)
      = ∑ i, (f (hA.eigenvalues i) : 𝕜) * (starRingEnd 𝕜 (c i) * c i) by
      simp only [dotProduct, mulVec_diagonal, Pi.star_apply, RCLike.star_def]
      exact sum_congr rfl fun i _ => by ring]
  simp only [RCLike.conj_mul, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show ((f (hA.eigenvalues i) : 𝕜) * (‖c i‖ : 𝕜) ^ 2 : 𝕜)
      = ((f (hA.eigenvalues i) * ‖c i‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
    RCLike.ofReal_re]
