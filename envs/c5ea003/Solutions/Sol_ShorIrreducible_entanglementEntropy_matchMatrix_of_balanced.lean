-- Prove2me | solution 1 for ShorIrreducible.entanglementEntropy_matchMatrix_of_balanced
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:18:56.275985+00:00
-- url     : https://prove2.me/submissions/0560af75-4305-425d-94ad-2e7e2418b708

-- Sol generated from Novelty/ShorMatchRank.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ
import Definitions.Def_Novelty_ShorMatchRank
import Theorems.Thm_IITTensorNetwork_vnEntropy_rhoLeft_of_schmidtForm
import Theorems.Thm_ShorIrreducible_matchLeft_isometry
import Theorems.Thm_ShorIrreducible_matchMatrix_schmidtForm
import Theorems.Thm_ShorIrreducible_matchRight_isometry

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








omit [DecidableEq α] [DecidableEq β] in
lemma card_matchSet_le_left (u : α → σ) (v : β → σ) :
    Fintype.card (matchSet u v) ≤ Fintype.card α := by
  rw [Fintype.card_coe]
  calc (matchSet u v).card ≤ (univ.image u).card :=
        Finset.card_le_card Finset.inter_subset_left
    _ ≤ (univ : Finset α).card := Finset.card_image_le
    _ = Fintype.card α := Finset.card_univ









/-! ### Closed-form Schmidt data -/

variable {u : α → σ} {v : β → σ} {c : ℝ}



/-- **The entanglement entropy of a fibre-matching state** in closed form. -/
theorem entanglementEntropy_matchMatrix :
    entanglementEntropy (matchMatrix u v c)
      = ∑ s ∈ matchSet u v, Real.negMulLog (c ^ 2 * (fibreCard u s * fibreCard v s : ℝ)) := by
  rw [entanglementEntropy, vnEntropy_rhoLeft_of_schmidtForm (matchLeft_isometry u v)
    (matchRight_isometry u v) (matchMatrix_schmidtForm u v c) (card_matchSet_le_left u v),
    ← Finset.sum_coe_sort (matchSet u v)
      (fun s => Real.negMulLog (c ^ 2 * (fibreCard u s * fibreCard v s : ℝ)))]
  refine Finset.sum_congr rfl fun s _ => ?_
  have ha : (0 : ℝ) ≤ fibreCard u (s : σ) := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ fibreCard v (s : σ) := Nat.cast_nonneg _
  rw [matchWeights, mul_pow, Real.sq_sqrt (by positivity)]


/-! ### The balanced case: a flat, incompressible Schmidt spectrum -/




/-! ### Function.Injective labellings: automatically flat -/




/-! ### The tensor-network obstruction -/





open ShorIrreducible in
theorem solution    (hbal : ∀ s ∈ matchSet u v,
      c ^ 2 * (fibreCard u s * fibreCard v s : ℝ) = ((matchSet u v).card : ℝ)⁻¹)
    (hne : (matchSet u v).Nonempty) :
    entanglementEntropy (matchMatrix u v c) = Real.log ((matchSet u v).card) := by
  rw [entanglementEntropy_matchMatrix,
    Finset.sum_congr rfl (fun s hs => by rw [hbal s hs]), Finset.sum_const, nsmul_eq_mul]
  have hK : (0 : ℝ) < (matchSet u v).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  rw [Real.negMulLog, Real.log_inv]
  field_simp
