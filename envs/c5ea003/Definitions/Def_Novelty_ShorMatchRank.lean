-- Prove2me | Definitions.Def_Novelty_ShorMatchRank
-- name    : Novelty_ShorMatchRank
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:55:47.273518+00:00
-- url     : https://prove2.me/theorems/4e75498f-1df5-4d98-bb55-588feab64f34
-- title:
--   Aether Catalog definitions — Novelty_ShorMatchRank
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ShorMatchRank`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ShorMatchRank.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ

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

namespace ShorIrreducible

open IITTensorNetwork

section MatchState

variable {α β σ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [DecidableEq σ]

/-- The number of preimages of a label. -/
def fibreCard (u : α → σ) (s : σ) : ℕ := (univ.filter fun f => u f = s).card

/-- The set of labels realized on both sides of the cut. -/
def matchSet (u : α → σ) (v : β → σ) : Finset σ := (univ.image u) ∩ (univ.image v)

/-- A **fibre-matching state**: amplitude `c` exactly on the pairs whose labels
agree. -/
def matchMatrix (u : α → σ) (v : β → σ) (c : ℝ) : Matrix α β ℂ :=
  fun f g => if u f = v g then (c : ℂ) else 0







/-- Left Schmidt vectors: the normalized indicator of each `u`-fibre. -/
noncomputable def matchLeft (u : α → σ) (v : β → σ) : Matrix α (matchSet u v) ℂ :=
  fun f s => if u f = (s : σ) then ((Real.sqrt (fibreCard u (s : σ)) : ℝ) : ℂ)⁻¹ else 0

/-- Right Schmidt vectors: the normalized indicator of each `v`-fibre. -/
noncomputable def matchRight (u : α → σ) (v : β → σ) : Matrix β (matchSet u v) ℂ :=
  fun g s => if v g = (s : σ) then ((Real.sqrt (fibreCard v (s : σ)) : ℝ) : ℂ)⁻¹ else 0

/-- The Schmidt coefficients of a fibre-matching state. -/
noncomputable def matchWeights (u : α → σ) (v : β → σ) (c : ℝ) : matchSet u v → ℝ :=
  fun s => c * Real.sqrt (fibreCard u (s : σ) * fibreCard v (s : σ))





/-! ### Closed-form Schmidt data -/

variable {u : α → σ} {v : β → σ} {c : ℝ}





/-! ### The balanced case: a flat, incompressible Schmidt spectrum -/




/-! ### Function.Injective labellings: automatically flat -/




/-! ### The tensor-network obstruction -/



end MatchState

end ShorIrreducible


