-- Prove2me | Theorems.Thm_ShorIrreducible_matchRight_isometry
-- name    : ShorIrreducible.matchRight_isometry
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:08:09.866014+00:00
-- url     : https://prove2.me/theorems/5c8acc21-d6da-4305-9468-e96870f99473
-- title:
--   MatchRight isometry
-- statement:
--   Formal statement of `ShorIrreducible.matchRight_isometry` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ShorIrreducible.matchRight_isometry(u : α → σ) (v : β → σ) :
--       (matchRight u v)ᴴ * matchRight u v = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorMatchRank.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorMatchRank.lean#L169

-- Thm stub generated from Novelty/ShorMatchRank.lean
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

theorem ShorIrreducible.matchRight_isometry(u : α → σ) (v : β → σ) :
    (matchRight u v)ᴴ * matchRight u v = 1 := by sorry
