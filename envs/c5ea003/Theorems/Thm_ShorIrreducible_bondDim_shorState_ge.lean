-- Prove2me | Theorems.Thm_ShorIrreducible_bondDim_shorState_ge
-- name    : ShorIrreducible.bondDim_shorState_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:09:14.128958+00:00
-- url     : https://prove2.me/theorems/58adbdbb-fd64-4bc2-bcd7-8a63b43fdabb
-- title:
--   The tensor-network obstruction for the full Shor state.
-- statement:
--   **The tensor-network obstruction for the full Shor state.**  Any matrix
--   product / tensor-train representation across the register cut has bond
--   dimension at least `r`.
--
--   ```lean
--   theorem ShorIrreducible.bondDim_shorState_ge(hr : 0 < r) (hm : 0 < m) (hF : HasExactPeriod r F) {χ : ℕ}
--       (h : HasBondDim (shorState (r * m) F) χ) : r ≤ χ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorFullState.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorFullState.lean#L237

-- Thm stub generated from Novelty/ShorFullState.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorMatchRank

/-! # The full Shor state is exponentially entangled: Schmidt rank exactly `r`

The state produced by the modular-exponentiation stage of Shor's algorithm is

`|ψ⟩ = Q^{-1/2} ∑_{x < Q} |x⟩ |a^x mod N⟩`,

with `Q` the size of the exponent register and `r = ord_N(a)`.  This file
computes *exactly* the entanglement data of `|ψ⟩` across the register cut,
under the only structural hypothesis that matters:

`HasExactPeriod r F : F x = F y ↔ x ≡ y (mod r)`,

which holds for `F x = a^x` with `r = orderOf a` (`hasExactPeriod_powFun`).

Main results (for `Q = r * m`, `0 < r`, `0 < m`):

* `schmidtRank_shorState` : the Schmidt rank across the cut is **exactly `r`**;
* `normalized_shorState` : the state is a unit vector;
* `entanglementEntropy_shorState` : `S = log r` — the maximum compatible with
  the rank, i.e. the Schmidt spectrum is *flat* (`flatSchmidtSpectrum_shorState`);
* `mutualInformation_shorState` : `I(A:B) = 2 log r`;
* `bondDim_shorState_ge` / `not_hasBondDim_shorState` : every MPS / tensor-train
  representation across the cut needs bond dimension `≥ r`, so no
  `poly(log N)`-bond-dimension emulation of the state exists unless `r` is
  itself polynomially small.

The last item is the precise obstruction to the "tensor-train QFT emulation"
proposal: its low-rank precondition already fails at the *input* of the QFT.
-/

open Finset Matrix
open scoped ComplexOrder

open ShorIrreducible

open IITTensorNetwork


variable {β : Type*} [Fintype β] [DecidableEq β]



variable {Q r : ℕ} {F : Fin Q → β}




/-! ## The Shor register state -/


variable {β : Type*} [Fintype β] [DecidableEq β]





variable {r m : ℕ} {F : Fin (r * m) → β}

theorem ShorIrreducible.bondDim_shorState_ge(hr : 0 < r) (hm : 0 < m) (hF : HasExactPeriod r F) {χ : ℕ}
    (h : HasBondDim (shorState (r * m) F) χ) : r ≤ χ := by sorry
