-- Prove2me | Theorems.Thm_ShorIrreducible_card_residue_class
-- name    : ShorIrreducible.card_residue_class
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:09:39.029586+00:00
-- url     : https://prove2.me/theorems/9483568c-6a5b-4e63-a03a-ab72da9d1742
-- title:
--   The number of elements of `Fin (r * m)` in a fixed residue class mod `r`.
-- statement:
--   The number of elements of `Fin (r * m)` in a fixed residue class mod `r`.
--
--   ```lean
--   theorem ShorIrreducible.card_residue_class{r m j : ℕ} (hr : 0 < r) (hj : j < r) :
--       ((univ : Finset (Fin (r * m))).filter fun x : Fin (r * m) => (x : ℕ) % r = j).card = m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorFullState.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorFullState.lean#L48

-- Thm stub generated from Novelty/ShorFullState.lean
import Mathlib
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

theorem ShorIrreducible.card_residue_class{r m j : ℕ} (hr : 0 < r) (hj : j < r) :
    ((univ : Finset (Fin (r * m))).filter fun x : Fin (r * m) => (x : ℕ) % r = j).card = m := by sorry
