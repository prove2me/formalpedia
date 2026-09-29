-- Prove2me | Theorems.Thm_ShorIrreducible_fidelity_flat_truncation_eq
-- name    : ShorIrreducible.fidelity_flat_truncation_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:12:50.449045+00:00
-- url     : https://prove2.me/theorems/5ad936cf-63b9-4b1c-8478-8b3461dafff5
-- title:
--   The flat-spectrum bound is attained.
-- statement:
--   **The flat-spectrum bound is attained.**  Truncating a flat rank-`r` state to
--   `D = #δ` of its Schmidt vectors and renormalizing gives fidelity exactly `D / r`,
--   so `fidelity_flat_le` cannot be improved.
--
--   ```lean
--   theorem ShorIrreducible.fidelity_flat_truncation_eq{M : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
--       (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (e : δ ↪ γ) (hD : 0 < Fintype.card δ)
--       (hM : M = L * Matrix.diagonal
--         (fun _ : γ => (((Real.sqrt (Fintype.card γ))⁻¹ : ℝ) : ℂ)) * Rᴴ) :
--       ‖frobInner M ((L.submatrix id e)
--           * Matrix.diagonal (fun _ : δ => (((Real.sqrt (Fintype.card δ))⁻¹ : ℝ) : ℂ))
--           * (R.submatrix id e)ᴴ)‖ ^ 2
--         = (Fintype.card δ : ℝ) / (Fintype.card γ : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorTruncationBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorTruncationBound.lean#L324

-- Thm stub generated from Novelty/ShorTruncationBound.lean
import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorTruncationBound

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

open ShorIrreducible

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]





/-! ### A Bessel inequality for isometries -/




/-! ### The overlap of two states in Schmidt form -/



/-! ### The flat-spectrum bound -/





/-! ### Sharpness: the truncated state attains the bound -/



omit [DecidableEq α] [DecidableEq β] in

theorem ShorIrreducible.fidelity_flat_truncation_eq{M : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (e : δ ↪ γ) (hD : 0 < Fintype.card δ)
    (hM : M = L * Matrix.diagonal
      (fun _ : γ => (((Real.sqrt (Fintype.card γ))⁻¹ : ℝ) : ℂ)) * Rᴴ) :
    ‖frobInner M ((L.submatrix id e)
        * Matrix.diagonal (fun _ : δ => (((Real.sqrt (Fintype.card δ))⁻¹ : ℝ) : ℂ))
        * (R.submatrix id e)ᴴ)‖ ^ 2
      = (Fintype.card δ : ℝ) / (Fintype.card γ : ℝ) := by sorry
