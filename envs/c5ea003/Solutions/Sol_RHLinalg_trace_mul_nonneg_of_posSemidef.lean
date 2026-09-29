-- Prove2me | solution 1 for RHLinalg.trace_mul_nonneg_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:45:50.309069+00:00
-- url     : https://prove2.me/submissions/f96ca416-ec74-472f-8311-e167cc9e1f7b

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann

-- from Zeta23.LinAlg.RankTrace
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
# The rank–trace inequality (paper §3, `lem:ranktrace`)

Let `P, Q` be Hermitian `d × d` matrices with `P ⪰ 0`, `rank P ≤ r`, and
`n₊(Q) ≤ b`. Then for every `c > 0`,

  `‖P+Q‖_F² ≥ c · tr P − (c²/4) · r + 2c · tr Q − c² · b`.

## Proof structure (the paper's proof of [lem:ranktrace], §3)

Decompose `Q = Q₊ − Q₋` (spectral positive/negative parts). Expand
`‖P+Q‖_F² = ‖P‖_F² + 2 tr(PQ₊) − 2 tr(PQ₋) + ‖Q₊‖_F² + ‖Q₋‖_F²` (using
`Q₊Q₋ = 0`). Drop `tr(PQ₊) ≥ 0`. By von Neumann,
`‖P‖_F² − 2 tr(PQ₋) + ‖Q₋‖_F² ≥ ∑(pᵢ−nᵢ)²`. The two elementary estimates
`sum_sq_diff_lower` and `sum_sq_lower_of_card_pos_le` bound the remaining
pieces, and `linarith` assembles.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Elementary real-sequence estimates -/

section Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





end Elementary

/-! ### Trace and Frobenius-norm identities -/






/-! ### The main theorem -/



end RHLinalg
end
open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ RCLike.re (A * B).trace := by
  -- Reduce `tr(AB)` to `tr((UᴴBU)D)` by the spectral theorem + trace cycling.
  rw [hA.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply, mul_assoc,
    trace_mul_comm, ← mul_assoc]
  set M := star (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) * B *
    (hA.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) with hM_def
  -- `M = UᴴBU` is PSD.
  have hM : M.PosSemidef := hB.conjTranspose_mul_mul_same _
  -- Now `0 ≤ re tr(M * diag λ) = ∑ᵢ λᵢ · re Mᵢᵢ`.
  simp only [trace, diag_apply, mul_diagonal, Function.comp_apply, map_sum,
    RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, mul_zero, sub_zero]
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (RCLike.nonneg_iff.mp hM.diag_nonneg).1 (hA.eigenvalues_nonneg i)
