-- Prove2me | solution 1 for ShorIrreducible.matchRight_isometry
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:08:09.299107+00:00
-- url     : https://prove2.me/submissions/9089522d-3792-4996-be3e-521bc7cdee33

-- Sol generated from Novelty/ShorMatchRank.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ
import Definitions.Def_Novelty_ShorMatchRank
import Theorems.Thm_ShorIrreducible_indicator_isometry

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
lemma fibreCard_right_pos {u : α → σ} {v : β → σ} (s : matchSet u v) :
    0 < fibreCard v (s : σ) :=
  fibreCard_pos (Finset.mem_inter.mp s.2).2











/-! ### Closed-form Schmidt data -/

variable {u : α → σ} {v : β → σ} {c : ℝ}





/-! ### The balanced case: a flat, incompressible Schmidt spectrum -/




/-! ### Function.Injective labellings: automatically flat -/




/-! ### The tensor-network obstruction -/





open ShorIrreducible in
omit [DecidableEq α] in
theorem solution(u : α → σ) (v : β → σ) :
    (matchRight u v)ᴴ * matchRight u v = 1 :=
  indicator_isometry _ (fun _ _ => rfl) (fun s => fibreCard_right_pos s)
