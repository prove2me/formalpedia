-- Prove2me | solution 1 for ShorIrreducible.sum_abs_le_sqrt_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:39:32.159307+00:00
-- url     : https://prove2.me/submissions/9ce78171-7888-4bae-afb0-81164a03e355

-- Sol generated from Novelty/ShorTruncationBound.lean
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




/-! ### The Frobenius error of a low-rank approximation -/




/-! ### Application: no low-rank emulation of Shor's state -/


variable {β : Type*} [Fintype β] [DecidableEq β]




open ShorIrreducible in
omit [DecidableEq δ] in
theorem solution{s : δ → ℝ} (hs : ∑ k, s k ^ 2 ≤ 1) :
    ∑ k, |s k| ≤ Real.sqrt (Fintype.card δ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset δ)
    (fun k => |s k|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    sq_abs] at hcs
  have hnn : 0 ≤ ∑ k, |s k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcard : (0 : ℝ) ≤ Fintype.card δ := Nat.cast_nonneg _
  have hbound : (∑ k, |s k|) ^ 2 ≤ (Fintype.card δ : ℝ) := by
    calc (∑ k, |s k|) ^ 2 ≤ (∑ k, s k ^ 2) * (Fintype.card δ : ℝ) := by
          simpa [mul_comm] using hcs
      _ ≤ 1 * (Fintype.card δ : ℝ) := by
          exact mul_le_mul_of_nonneg_right hs hcard
      _ = (Fintype.card δ : ℝ) := one_mul _
  nlinarith [Real.sq_sqrt hcard, Real.sqrt_nonneg ((Fintype.card δ : ℝ)), hnn, hbound]
