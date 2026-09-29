-- Prove2me | Definitions.Def_Probability_ForkPinningProduct
-- name    : Probability_ForkPinningProduct
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:32.58518+00:00
-- url     : https://prove2.me/theorems/71299a6d-f92e-4a11-baa5-6a9a149cbc40
-- title:
--   Aether Catalog definitions — Probability_ForkPinningProduct
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ForkPinningProduct`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ForkPinningProduct.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
/-
# Independent side-information: the coprime control and the vanishing residual

In the arithmetic experiment the observable attached to a prime `p` is its residue in some
modulus `m`.  Chebotarev factorizes that observable: the part of `p mod m` that is visible to
the splitting field is the image of the Frobenius element in the abelianization of the Galois
group, and the rest is *independent noise*.  The two model theorems proved here are:

* `ForkPinning.coprime_control_flat` : a statistic that lives on an independent factor of the
  probability space carries **zero** information about the fork (the observed `I = 0.0000`
  at the coprime control modulus);
* `ForkPinning.mutualInfo_abelian_plus_noise` : adding independent noise to the abelian
  statistic changes nothing, `I((φ, noise); fork) = I(φ; fork)` — the observed
  "beyond-sign residual `= +0.0000` exactly".
-/


namespace ForkPinning

open Finset Real

variable {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
variable {κ β α : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]
  [Fintype α] [DecidableEq α]

/-! ## Marginals of a product space -/









/-! ## Independent noise adjoined to the abelian statistic -/

/-- Reassociation `(α × Ω₂) × β ≃ (α × β) × Ω₂`. -/
def swapMid (α β Ω₂ : Type*) : (α × Ω₂) × β ≃ (α × β) × Ω₂ where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl


end ForkPinning


