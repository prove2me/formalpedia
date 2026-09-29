-- Prove2me | solution 1 for ShorIrreducible.card_image_of_hasExactPeriod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:05:41.325347+00:00
-- url     : https://prove2.me/submissions/63b1a39e-f691-4c93-ac4d-e43865bf6e82

-- Sol generated from Novelty/ShorFullState.lean
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



variable {Q r : ℕ} {F : Fin Q → β}




/-! ## The Shor register state -/


variable {β : Type*} [Fintype β] [DecidableEq β]





variable {r m : ℕ} {F : Fin (r * m) → β}









/-! ## The concrete modular-exponentiation state -/


variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]








open ShorIrreducible in
omit [Fintype β] in
theorem solution{m : ℕ} (hr : 0 < r) (hm : 0 < m)
    {F : Fin (r * m) → β} (hF : HasExactPeriod r F) :
    ((univ : Finset (Fin (r * m))).image F).card = r := by
  classical
  have hemb : ∀ j : Fin r, (j : ℕ) < r * m := by
    intro j
    calc (j : ℕ) < r := j.2
      _ = r * 1 := (mul_one r).symm
      _ ≤ r * m := Nat.mul_le_mul_left r hm
  set G : Fin r → β := fun j => F ⟨(j : ℕ), hemb j⟩ with hG
  have himg : (univ : Finset (Fin (r * m))).image F = (univ : Finset (Fin r)).image G := by
    apply Finset.Subset.antisymm
    · intro b hb
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hb
      have hlt : (x : ℕ) % r < r := Nat.mod_lt _ hr
      refine Finset.mem_image.mpr ⟨⟨(x : ℕ) % r, hlt⟩, Finset.mem_univ _, ?_⟩
      rw [hG]
      refine ((hF _ _).mpr ?_).symm
      show (x : ℕ) % r = ((x : ℕ) % r) % r
      rw [Nat.mod_mod_of_dvd _ dvd_rfl]
    · intro b hb
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨⟨(j : ℕ), hemb j⟩, Finset.mem_univ _, rfl⟩
  have hinj : Function.Injective G := by
    intro i j hij
    have := (hF _ _).mp hij
    simp only at this
    rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
    exact Fin.ext this
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
