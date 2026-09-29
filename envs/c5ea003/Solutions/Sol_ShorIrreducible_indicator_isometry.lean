-- Prove2me | solution 1 for ShorIrreducible.indicator_isometry
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:05:42.445551+00:00
-- url     : https://prove2.me/submissions/47a18a3d-7532-41d4-861e-831d7e606d2e

-- Sol generated from Novelty/ShorMatchRank.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ
import Definitions.Def_Novelty_ShorMatchRank

/-! # Fibre-matching bipartite states: exact Schmidt data

This file develops the linear-algebra engine used in the assessment of the
"de-quantization of Shor" proposal (`ShorCombState`, `ShorFullState`,
`ShorQFTOutput`).

A great many states produced by a *classical reversible computation run in
superposition* have the following shape.  Two finite index sets `α` (left
register) and `β` (right register) are equipped with maps
`u : α → σ` and `v : β → σ` into a common set of *labels*, and the amplitude of
`|f⟩|g⟩` is a constant `c` when the labels match and `0` otherwise:

`M f g = if u f = v g then c else 0`.

For Shor's algorithm: `α` is the exponent register, `β` the function register,
`σ = ZMod r` records the exponent modulo the multiplicative order `r`, `u` is
reduction mod `r` and `v` is the discrete logarithm.  For the *comb* (the state
of the exponent register after the function register is measured), `α`, `β` are
the two halves of the exponent register and `σ = ZMod r` again.

We prove that such a state is *exactly* in Schmidt form with

* Schmidt rank  = `#(image u ∩ image v)`  (`schmidtRank_matchMatrix`),
* Schmidt coefficients `w s = c √(|u⁻¹ s| · |v⁻¹ s|)`,

so all entanglement quantities of the state are computed in closed form:
`entanglementEntropy_matchMatrix`, `mutualInformation_matchMatrix`, and in the
balanced ("all fibres of equal size") case the spectrum is *flat*, saturating
every Schmidt-rank bound: `entanglementEntropy_matchMatrix_of_balanced`,
`flatSchmidtSpectrum_matchMatrix_of_balanced`.

The negative consequence for tensor-network emulation is
`bondDim_matchMatrix_ge`: *any* matrix-product / tensor-train representation of
such a state across the cut needs bond dimension at least `#(image u ∩ image v)`.
-/

open Finset Matrix
open scoped ComplexOrder

open ShorIrreducible

open IITTensorNetwork


variable {α β σ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [DecidableEq σ]

















/-! ### Closed-form Schmidt data -/

variable {u : α → σ} {v : β → σ} {c : ℝ}





/-! ### The balanced case: a flat, incompressible Schmidt spectrum -/




/-! ### Function.Injective labellings: automatically flat -/




/-! ### The tensor-network obstruction -/





open ShorIrreducible in
theorem solution{γ : Type*} [Fintype γ] [DecidableEq γ] {w : γ → σ}
    {S : Finset σ} (L : Matrix γ S ℂ)
    (hL : ∀ (g : γ) (s : S),
      L g s = if w g = (s : σ) then ((Real.sqrt (fibreCard w (s : σ)) : ℝ) : ℂ)⁻¹ else 0)
    (hpos : ∀ s : S, 0 < fibreCard w (s : σ)) :
    Lᴴ * L = 1 := by
  classical
  ext s s'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, hL]
  have hterm : ∀ g : γ,
      (starRingEnd ℂ) (if w g = (s : σ) then ((Real.sqrt (fibreCard w (s : σ)) : ℝ) : ℂ)⁻¹ else 0) *
        (if w g = (s' : σ) then ((Real.sqrt (fibreCard w (s' : σ)) : ℝ) : ℂ)⁻¹ else 0)
      = if w g = (s : σ) ∧ w g = (s' : σ) then
          (((Real.sqrt (fibreCard w (s : σ)))⁻¹ * (Real.sqrt (fibreCard w (s' : σ)))⁻¹ : ℝ) : ℂ)
        else 0 := by
    intro g
    by_cases h1 : w g = (s : σ)
    · by_cases h2 : w g = (s' : σ)
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
          Complex.conj_ofReal, ← Complex.ofReal_mul]
      · rw [if_pos h1, if_neg h2, mul_zero]
        exact (if_neg (fun hh => h2 hh.2)).symm
    · rw [if_neg h1, map_zero, zero_mul]
      exact (if_neg (fun hh => h1 hh.1)).symm
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  by_cases hss : s = s'
  · subst hss
    rw [Matrix.one_apply_eq]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
    have hfil : (univ.filter fun g => w g = (s : σ) ∧ w g = (s : σ))
        = univ.filter fun g => w g = (s : σ) := by
      apply Finset.filter_congr; intro g _; simp
    have hcard : (univ.filter fun g => w g = (s : σ)).card = fibreCard w (s : σ) := rfl
    rw [hfil, hcard, nsmul_eq_mul]
    have hpos' : (0 : ℝ) < fibreCard w (s : σ) := by exact_mod_cast hpos s
    have hsqsq : Real.sqrt (fibreCard w (s : σ)) * Real.sqrt (fibreCard w (s : σ))
        = (fibreCard w (s : σ) : ℝ) := Real.mul_self_sqrt hpos'.le
    have key : (fibreCard w (s : σ) : ℝ) *
        ((Real.sqrt (fibreCard w (s : σ)))⁻¹ * (Real.sqrt (fibreCard w (s : σ)))⁻¹) = 1 := by
      rw [← mul_inv, hsqsq]
      field_simp
    exact_mod_cast key
  · rw [Matrix.one_apply_ne hss]
    apply Finset.sum_eq_zero
    intro g _
    have : ¬ (w g = (s : σ) ∧ w g = (s' : σ)) := by
      rintro ⟨h1, h2⟩
      exact hss (Subtype.ext (h1 ▸ h2))
    simp [this]
