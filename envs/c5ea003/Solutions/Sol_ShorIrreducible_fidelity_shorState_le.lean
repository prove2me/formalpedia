-- Prove2me | solution 1 for ShorIrreducible.fidelity_shorState_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:43:47.138756+00:00
-- url     : https://prove2.me/submissions/c7d5c365-e942-49f7-8233-5a9a1c3a157b

-- Sol generated from Novelty/ShorTruncationBound.lean
import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorMatchRank
import Definitions.Def_Novelty_ShorTruncationBound
import Theorems.Thm_ShorIrreducible_card_image_of_hasExactPeriod
import Theorems.Thm_ShorIrreducible_fibreCard_id
import Theorems.Thm_ShorIrreducible_fibreCard_of_hasExactPeriod
import Theorems.Thm_ShorIrreducible_matchLeft_isometry
import Theorems.Thm_ShorIrreducible_matchMatrix_schmidtForm
import Theorems.Thm_ShorIrreducible_matchRight_isometry
import Theorems.Thm_ShorIrreducible_matchSet_id
import Theorems.Thm_ShorIrreducible_norm_frobInner_flat_le

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



/-- **Fidelity form of the flat-spectrum bound**: the squared overlap of a flat
rank-`r` state with any rank-`D` approximant is at most `D / r`. -/
theorem fidelity_flat_le {M A : Matrix α β ℂ} {L : Matrix α γ ℂ}
    {R : Matrix β γ ℂ} {P : Matrix α δ ℂ} {Q : Matrix β δ ℂ} {w : γ → ℝ} {s : δ → ℝ}
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1)
    (hM : M = L * Matrix.diagonal (fun j => (w j : ℂ)) * Rᴴ)
    (hA : A = P * Matrix.diagonal (fun k => (s k : ℂ)) * Qᴴ)
    (hw : ∀ j, |w j| ≤ (Real.sqrt (Fintype.card γ))⁻¹) (hs : ∑ k, s k ^ 2 ≤ 1) :
    ‖frobInner M A‖ ^ 2 ≤ (Fintype.card δ : ℝ) / (Fintype.card γ : ℝ) := by
  have h := norm_frobInner_flat_le hL hR hP hQ hM hA hw hs
  have hnn : (0 : ℝ) ≤ (Fintype.card δ : ℝ) / (Fintype.card γ : ℝ) := by positivity
  nlinarith [Real.sq_sqrt hnn, norm_nonneg (frobInner M A),
    Real.sqrt_nonneg ((Fintype.card δ : ℝ) / (Fintype.card γ : ℝ))]


/-! ### Sharpness: the truncated state attains the bound -/




/-! ### The Frobenius error of a low-rank approximation -/




/-! ### Application: no low-rank emulation of Shor's state -/


variable {β : Type*} [Fintype β] [DecidableEq β]




open ShorIrreducible in
theorem solution{r m : ℕ} {F : Fin (r * m) → β} (hr : 0 < r) (hm : 0 < m)
    (hF : HasExactPeriod r F) {δ : Type*} [Fintype δ] [DecidableEq δ]
    {A : Matrix (Fin (r * m)) β ℂ} {P : Matrix (Fin (r * m)) δ ℂ} {Q : Matrix β δ ℂ}
    {s : δ → ℝ} (hP : Pᴴ * P = 1) (hQ : Qᴴ * Q = 1)
    (hA : A = P * Matrix.diagonal (fun k => (s k : ℂ)) * Qᴴ) (hs : ∑ k, s k ^ 2 ≤ 1) :
    ‖frobInner (shorState (r * m) F) A‖ ^ 2 ≤ (Fintype.card δ : ℝ) / (r : ℝ) := by
  classical
  have hcard : Fintype.card ↑(matchSet F (id : β → β)) = r := by
    rw [Fintype.card_coe, matchSet_id, card_image_of_hasExactPeriod hr hm hF]
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hw : ∀ j : ↑(matchSet F (id : β → β)),
      |matchWeights F (id : β → β) ((Real.sqrt ((r * m : ℕ) : ℝ))⁻¹) j|
        ≤ (Real.sqrt (Fintype.card ↑(matchSet F (id : β → β))))⁻¹ := by
    intro j
    have hj : (j : β) ∈ (univ : Finset (Fin (r * m))).image F := by
      have hmem : (j : β) ∈ matchSet F (id : β → β) := j.2
      exact (Finset.mem_inter.mp hmem).1
    have hfib : fibreCard F (j : β) = m := fibreCard_of_hasExactPeriod hr hF hj
    have hone : fibreCard (id : β → β) (j : β) = 1 := fibreCard_id _
    have hval : matchWeights F (id : β → β) ((Real.sqrt ((r * m : ℕ) : ℝ))⁻¹) j
        = (Real.sqrt r)⁻¹ := by
      rw [matchWeights, hfib, hone]
      have hcast : ((r * m : ℕ) : ℝ) = (r : ℝ) * (m : ℝ) := by push_cast; ring
      rw [hcast, Real.sqrt_mul hrR.le]
      have hsm : Real.sqrt ((m : ℝ) * (1 : ℝ)) = Real.sqrt m := by rw [mul_one]
      have : ((m : ℕ) : ℝ) * ((1 : ℕ) : ℝ) = (m : ℝ) * (1 : ℝ) := by push_cast; ring
      rw [this, hsm]
      have hsqm : Real.sqrt (m : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hval, hcard, abs_of_nonneg (by positivity)]
  have hmain := fidelity_flat_le (M := shorState (r * m) F) (A := A)
    (L := matchLeft F (id : β → β)) (R := matchRight F (id : β → β)) (P := P) (Q := Q)
    (w := matchWeights F (id : β → β) ((Real.sqrt ((r * m : ℕ) : ℝ))⁻¹)) (s := s)
    (matchLeft_isometry F id) (matchRight_isometry F id) hP hQ
    (matchMatrix_schmidtForm F id _) hA hw hs
  rwa [hcard] at hmain
