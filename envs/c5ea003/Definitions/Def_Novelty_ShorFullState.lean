-- Prove2me | Definitions.Def_Novelty_ShorFullState
-- name    : Novelty_ShorFullState
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:57:09.014234+00:00
-- url     : https://prove2.me/theorems/46a5c49b-e145-4a0f-a25d-bc2f6c430a60
-- title:
--   Aether Catalog definitions — Novelty_ShorFullState
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ShorFullState`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ShorFullState.lean by skeleton subtraction
import Mathlib
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

namespace ShorIrreducible

open IITTensorNetwork

section Periodic

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- `F` has *exact period `r`*: its level sets are precisely the residue classes
modulo `r`.  For `F x = a ^ x` this says `r` is the multiplicative order of `a`. -/
def HasExactPeriod (r : ℕ) {Q : ℕ} (F : Fin Q → β) : Prop :=
  ∀ x y : Fin Q, F x = F y ↔ (x : ℕ) % r = (y : ℕ) % r


variable {Q r : ℕ} {F : Fin Q → β}



end Periodic

/-! ## The Shor register state -/

section ShorState

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The **Shor register state** `Q^{-1/2} ∑_x |x⟩|F x⟩`, presented as its
coefficient matrix across the cut between the exponent register and the
function register. -/
noncomputable def shorState (Q : ℕ) (F : Fin Q → β) : Matrix (Fin Q) β ℂ :=
  matchMatrix F (id : β → β) (Real.sqrt Q)⁻¹




variable {r m : ℕ} {F : Fin (r * m) → β}








end ShorState

/-! ## The concrete modular-exponentiation state -/

section ModularExponentiation

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The modular exponential `x ↦ a ^ x` on a register of size `Q`. -/
def powFun (a : G) (Q : ℕ) : Fin Q → G := fun x => a ^ (x : ℕ)





end ModularExponentiation

end ShorIrreducible


