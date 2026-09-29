-- Prove2me | solution 1 for ShorIrreducible.not_hasBondDim_shorState_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:51:27.74981+00:00
-- url     : https://prove2.me/submissions/15808aa2-874a-47b2-86e6-e337d68e5a63

-- Sol generated from Novelty/ShorFullState.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorMatchRank
import Theorems.Thm_ShorIrreducible_bondDim_shorState_ge
import Theorems.Thm_ShorIrreducible_hasExactPeriod_powFun

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







/-- Below bond dimension `r` there is no MPS representation of the Shor state at
all: the low-rank precondition of tensor-train emulation fails. -/
theorem not_hasBondDim_shorState (hr : 0 < r) (hm : 0 < m) (hF : HasExactPeriod r F)
    {χ : ℕ} (hχ : χ < r) : ¬ HasBondDim (shorState (r * m) F) χ :=
  fun h => absurd (bondDim_shorState_ge hr hm hF h) (not_le.mpr hχ)


/-! ## The concrete modular-exponentiation state -/


variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]








open ShorIrreducible in
theorem solution{a : G} {r m : ℕ} (hr : orderOf a = r) (hrpos : 0 < r)
    (hm : 0 < m) {χ : ℕ} (hχ : χ < r) :
    ¬ HasBondDim (shorState (r * m) (powFun a (r * m))) χ :=
  not_hasBondDim_shorState hrpos hm (hr ▸ hasExactPeriod_powFun a (r * m)) hχ
