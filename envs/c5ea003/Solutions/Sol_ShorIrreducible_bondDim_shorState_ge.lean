-- Prove2me | solution 1 for ShorIrreducible.bondDim_shorState_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:12:55.383839+00:00
-- url     : https://prove2.me/submissions/5609b94f-c592-45b6-a000-b1c92db36d51

-- Sol generated from Novelty/ShorFullState.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorMatchRank
import Theorems.Thm_IITTensorNetwork_schmidtRank_le_of_hasBondDim
import Theorems.Thm_ShorIrreducible_card_image_of_hasExactPeriod
import Theorems.Thm_ShorIrreducible_matchSet_id
import Theorems.Thm_ShorIrreducible_schmidtRank_matchMatrix

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

/-- **The Schmidt rank of the full Shor state across the register cut is exactly
the multiplicative order `r`.** -/
theorem schmidtRank_shorState (hr : 0 < r) (hm : 0 < m) (hF : HasExactPeriod r F) :
    schmidtRank (shorState (r * m) F) = r := by
  have hQ : (0 : ℝ) < ((r * m : ℕ) : ℝ) := by
    have : 0 < r * m := Nat.mul_pos hr hm
    exact_mod_cast this
  have hc : ((Real.sqrt ((r * m : ℕ) : ℝ))⁻¹ : ℝ) ≠ 0 :=
    inv_ne_zero (by positivity)
  rw [shorState, schmidtRank_matchMatrix hc, matchSet_id,
    card_image_of_hasExactPeriod hr hm hF]








/-! ## The concrete modular-exponentiation state -/


variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]








open ShorIrreducible in
theorem solution(hr : 0 < r) (hm : 0 < m) (hF : HasExactPeriod r F) {χ : ℕ}
    (h : HasBondDim (shorState (r * m) F) χ) : r ≤ χ := by
  have := schmidtRank_le_of_hasBondDim h
  rwa [schmidtRank_shorState hr hm hF] at this
