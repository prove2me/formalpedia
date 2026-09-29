-- Prove2me | solution 1 for ShorIrreducible.fibreCard_of_hasExactPeriod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:22:39.433095+00:00
-- url     : https://prove2.me/submissions/7c5f88a2-01a9-4617-a717-98e451a6a40a

-- Sol generated from Novelty/ShorFullState.lean
import Mathlib
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorMatchRank
import Theorems.Thm_ShorIrreducible_card_residue_class

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









/-! ## The concrete modular-exponentiation state -/


variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]








open ShorIrreducible in
omit [Fintype β] in
theorem solution{m : ℕ} (hr : 0 < r) {F : Fin (r * m) → β}
    (hF : HasExactPeriod r F) {b : β} (hb : b ∈ (univ : Finset (Fin (r * m))).image F) :
    fibreCard F b = m := by
  classical
  obtain ⟨x0, -, rfl⟩ := Finset.mem_image.mp hb
  have hfil : (univ.filter fun x : Fin (r * m) => F x = F x0)
      = (univ : Finset (Fin (r * m))).filter fun x : Fin (r * m) =>
          (x : ℕ) % r = (x0 : ℕ) % r := by
    apply Finset.filter_congr
    intro x _
    simpa using hF x x0
  rw [fibreCard, hfil]
  exact card_residue_class hr (Nat.mod_lt _ hr)
