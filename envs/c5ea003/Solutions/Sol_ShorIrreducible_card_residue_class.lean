-- Prove2me | solution 1 for ShorIrreducible.card_residue_class
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:16:50.206282+00:00
-- url     : https://prove2.me/submissions/5be41665-c620-443a-bf59-c91cf925792f

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
theorem solution{r m j : ℕ} (hr : 0 < r) (hj : j < r) :
    ((univ : Finset (Fin (r * m))).filter fun x : Fin (r * m) => (x : ℕ) % r = j).card = m := by
  classical
  have hbound : ∀ t : Fin m, j + r * (t : ℕ) < r * m := by
    intro t
    have ht : (t : ℕ) + 1 ≤ m := t.2
    calc j + r * (t : ℕ) < r + r * (t : ℕ) := Nat.add_lt_add_right hj _
      _ = r * ((t : ℕ) + 1) := by ring
      _ ≤ r * m := Nat.mul_le_mul_left r ht
  have key : ((univ : Finset (Fin (r * m))).filter fun x : Fin (r * m) => (x : ℕ) % r = j).card
      = (univ : Finset (Fin m)).card := by
    refine Finset.card_nbij'
      (fun x : Fin (r * m) => (⟨(x : ℕ) / r, Nat.div_lt_of_lt_mul x.isLt⟩ : Fin m))
      (fun t : Fin m => (⟨j + r * (t : ℕ), hbound t⟩ : Fin (r * m))) ?_ ?_ ?_ ?_
    · intro x _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro t _
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      show (j + r * (t : ℕ)) % r = j
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    · intro x hx
      have hx' : (x : ℕ) % r = j := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      apply Fin.ext
      show j + r * ((x : ℕ) / r) = (x : ℕ)
      rw [← hx']
      exact Nat.mod_add_div _ _
    · intro t _
      apply Fin.ext
      show (j + r * (t : ℕ)) / r = (t : ℕ)
      rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hj, zero_add]
  rw [key, Finset.card_univ, Fintype.card_fin]
