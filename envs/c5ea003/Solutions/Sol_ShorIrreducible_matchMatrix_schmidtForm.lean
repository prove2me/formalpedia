-- Prove2me | solution 1 for ShorIrreducible.matchMatrix_schmidtForm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:08:08.55695+00:00
-- url     : https://prove2.me/submissions/c254f77b-fdff-44c4-9478-54a419053f01

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




omit [DecidableEq α] in
lemma fibreCard_pos {u : α → σ} {s : σ} (h : s ∈ univ.image u) : 0 < fibreCard u s := by
  obtain ⟨f, -, hf⟩ := Finset.mem_image.mp h
  exact Finset.card_pos.mpr ⟨f, by simp [hf]⟩

omit [DecidableEq α] [DecidableEq β] in
lemma fibreCard_left_pos {u : α → σ} {v : β → σ} (s : matchSet u v) :
    0 < fibreCard u (s : σ) :=
  fibreCard_pos (Finset.mem_inter.mp s.2).1

omit [DecidableEq α] [DecidableEq β] in
lemma fibreCard_right_pos {u : α → σ} {v : β → σ} (s : matchSet u v) :
    0 < fibreCard v (s : σ) :=
  fibreCard_pos (Finset.mem_inter.mp s.2).2

omit [DecidableEq α] [DecidableEq β] in
lemma mem_matchSet_of_eq {u : α → σ} {v : β → σ} {f : α} {g : β} (h : u f = v g) :
    u f ∈ matchSet u v :=
  Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ f),
    h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ g)⟩










/-! ### Closed-form Schmidt data -/

variable {u : α → σ} {v : β → σ} {c : ℝ}





/-! ### The balanced case: a flat, incompressible Schmidt spectrum -/




/-! ### Function.Injective labellings: automatically flat -/




/-! ### The tensor-network obstruction -/





open ShorIrreducible in
omit [DecidableEq α] [DecidableEq β] in
theorem solution(u : α → σ) (v : β → σ) (c : ℝ) :
    matchMatrix u v c
      = matchLeft u v * Matrix.diagonal (fun s => ((matchWeights u v c s : ℝ) : ℂ))
          * (matchRight u v)ᴴ := by
  classical
  ext f g
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def]
  by_cases h : u f = v g
  · have hmem : u f ∈ matchSet u v := mem_matchSet_of_eq h
    set s0 : matchSet u v := ⟨u f, hmem⟩ with hs0
    rw [Finset.sum_eq_single s0]
    · have ha : (0 : ℝ) < fibreCard u (u f) := by exact_mod_cast fibreCard_left_pos s0
      have hb : (0 : ℝ) < fibreCard v (u f) := by exact_mod_cast fibreCard_right_pos s0
      have hsa : Real.sqrt (fibreCard u (u f)) ≠ 0 := by positivity
      have hsb : Real.sqrt (fibreCard v (u f)) ≠ 0 := by positivity
      have hL0 : matchLeft u v f s0 = (((Real.sqrt (fibreCard u (u f)))⁻¹ : ℝ) : ℂ) := by
        simp [matchLeft, hs0]
      have hR0 : matchRight u v g s0 = (((Real.sqrt (fibreCard v (u f)))⁻¹ : ℝ) : ℂ) := by
        simp [matchRight, hs0, h.symm]
      have hw0 : matchWeights u v c s0
          = c * (Real.sqrt (fibreCard u (u f)) * Real.sqrt (fibreCard v (u f))) := by
        rw [matchWeights, Real.sqrt_mul (by positivity)]
      have hM : matchMatrix u v c f g = (c : ℂ) := by rw [matchMatrix, if_pos h]
      rw [hL0, hR0, hw0, hM, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      norm_cast
      field_simp
    · intro t _ ht
      have hut : ¬ u f = (t : σ) := by
        intro hc'; exact ht (Subtype.ext hc'.symm)
      simp [matchLeft, hut]
    · intro hcon; exact absurd (Finset.mem_univ s0) hcon
  · rw [matchMatrix, if_neg h]
    refine (Finset.sum_eq_zero ?_).symm
    intro s _
    by_cases h1 : u f = (s : σ)
    · have h2 : ¬ v g = (s : σ) := by
        intro h2; exact h (h1.trans h2.symm)
      simp [matchRight, h2]
    · simp [matchLeft, h1]
