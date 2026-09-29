-- Prove2me | solution 1 for ShorIrreducible.flatSchmidtSpectrum_matchMatrix_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:45:43.85913+00:00
-- url     : https://prove2.me/submissions/54be23de-98f4-4651-92e4-9e85d32954cb

-- Sol generated from Novelty/ShorMatchRank.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ
import Definitions.Def_Novelty_ShorMatchRank
import Theorems.Thm_IITTensorNetwork_entanglementEntropy_eq_log_schmidtRank_iff
import Theorems.Thm_ShorIrreducible_entanglementEntropy_matchMatrix_of_injective
import Theorems.Thm_ShorIrreducible_normalized_matchMatrix
import Theorems.Thm_ShorIrreducible_schmidtRank_matchMatrix

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

omit [DecidableEq α] [DecidableEq β] in
lemma fibreCard_of_injective {γ : Type*} [Fintype γ] {w : γ → σ} (hw : Function.Injective w)
    {s : σ} (hs : s ∈ (univ : Finset γ).image w) : fibreCard w s = 1 := by
  classical
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hs
  have : (univ.filter fun g' : γ => w g' = w g) = {g} := by
    ext g'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hw h, fun h => by rw [h]⟩
  rw [fibreCard, this, Finset.card_singleton]



/-! ### The tensor-network obstruction -/





open ShorIrreducible in
theorem solution(hc : c ≠ 0) (hu : Function.Injective u)
    (hv : Function.Injective v)
    (hnorm : c ^ 2 * ((matchSet u v).card : ℝ) = 1) (hne : (matchSet u v).Nonempty) :
    FlatSchmidtSpectrum (matchMatrix u v c) := by
  have hnorm' : ∑ s ∈ matchSet u v, c ^ 2 * (fibreCard u s * fibreCard v s : ℝ) = 1 := by
    rw [Finset.sum_congr rfl (fun s hs => by
      rw [fibreCard_of_injective hu (Finset.mem_inter.mp hs).1,
        fibreCard_of_injective hv (Finset.mem_inter.mp hs).2]), Finset.sum_const, nsmul_eq_mul]
    rw [← hnorm]; push_cast; ring
  refine (entanglementEntropy_eq_log_schmidtRank_iff (normalized_matchMatrix hnorm')).mp ?_
  rw [schmidtRank_matchMatrix hc]
  exact entanglementEntropy_matchMatrix_of_injective hu hv hnorm hne
