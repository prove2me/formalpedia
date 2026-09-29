-- Prove2me | Definitions.Def_Novelty_ShorTruncationBound
-- name    : Novelty_ShorTruncationBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:59:27.94946+00:00
-- url     : https://prove2.me/theorems/f94c5ad7-2f18-488d-97c8-aa90153ee09d
-- title:
--   Aether Catalog definitions — Novelty_ShorTruncationBound
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ShorTruncationBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ShorTruncationBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ShorFullState

/-! # Fidelity of low-rank (truncated tensor-train) approximations to a flat state

This file supplies the quantitative half of the de-quantization assessment.  The
companion files show that Shor's states have Schmidt rank exactly `r` with a
*flat* spectrum.  Here we bound how well *any* bond-dimension-`D` approximant can
do against such a state.

Both the target `M` and the approximant `A` are given in Schmidt form,
`M = L · diag w · Rᴴ`, `A = P · diag s · Qᴴ` with isometric `L, R, P, Q` — the
form produced by a singular value decomposition, and in particular by the
truncated SVD sweeps of a matrix-product-state emulation with bond dimension
`D = #δ`.

The main results are

* `norm_frobInner_le_of_schmidtForms` : `|⟪M, A⟫_F| ≤ (max_j |w j|) · ∑_k |s k|`;
* `norm_frobInner_flat_le` : for a *flat* spectrum of rank `r`,
  `|⟪M, A⟫_F| ≤ √(D / r)`;
* `fidelity_flat_le` : hence the fidelity obeys `|⟪M, A⟫_F|² ≤ D / r`;
* `frobDistSq_flat_ge` : the Frobenius error satisfies `‖M - A‖² ≥ 2 - 2√(D/r)`;
* `fidelity_shorState_le` : for the Shor state itself, every rank-`D`
  approximant has fidelity at most `D / r`.

The bound is **sharp**: `fidelity_flat_eq_of_truncation` exhibits, for every
`D ≤ r`, an approximant attaining `D / r` exactly.  This corrects the informal
claim `(D/r)²` of the source paper: the correct decay is linear in `D/r`, which
is *worse* for the emulator (the fidelity decays more slowly but is still
`O(D/r)`, hence exponentially small at any polynomial bond dimension).
-/

open Finset Matrix IITTensorNetwork

namespace ShorIrreducible

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-- The Frobenius (Hilbert–Schmidt) inner product of two bipartite states. -/
noncomputable def frobInner (M A : Matrix α β ℂ) : ℂ := Matrix.trace (Mᴴ * A)

/-- The squared Frobenius norm of a bipartite state. -/
noncomputable def frobSq (M : Matrix α β ℂ) : ℝ := ∑ f, ∑ g, ‖M f g‖ ^ 2



/-! ### A Bessel inequality for isometries -/




/-! ### The overlap of two states in Schmidt form -/



/-! ### The flat-spectrum bound -/





/-! ### Sharpness: the truncated state attains the bound -/




/-! ### The Frobenius error of a low-rank approximation -/




/-! ### Application: no low-rank emulation of Shor's state -/

section ShorApplication

variable {β : Type*} [Fintype β] [DecidableEq β]


end ShorApplication

end ShorIrreducible


