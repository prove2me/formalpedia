-- Prove2me | Theorems.Thm_ForkPinning_mutualInfo_abelian_plus_noise
-- name    : ForkPinning.mutualInfo_abelian_plus_noise
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:36:37.153455+00:00
-- url     : https://prove2.me/theorems/9632f89f-0952-4508-a795-647699214160
-- title:
--   Zero residual beyond the abelian part.
-- statement:
--   **Zero residual beyond the abelian part.**  If the observable is the abelian statistic `φ`
--   together with an independent coordinate (the part of the residue that the field cannot see),
--   its information about the fork is exactly the information carried by `φ` alone.
--
--   ```lean
--   theorem ForkPinning.mutualInfo_abelian_plus_noise[DecidableEq Ω₂] (φ : Ω₁ → α) (Y : Ω₁ → β) :
--       mutualInfo (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (fun x : Ω₁ × Ω₂ => Y x.1)
--         = mutualInfo φ Y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningProduct.lean#L101

-- Thm stub generated from Probability/ForkPinningProduct.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningProduct
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


open ForkPinning

open Finset Real

variable {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
variable {κ β α : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]
  [Fintype α] [DecidableEq α]

/-! ## Marginals of a product space -/









/-! ## Independent noise adjoined to the abelian statistic -/

theorem ForkPinning.mutualInfo_abelian_plus_noise[DecidableEq Ω₂] (φ : Ω₁ → α) (Y : Ω₁ → β) :
    mutualInfo (fun x : Ω₁ × Ω₂ => (φ x.1, x.2)) (fun x : Ω₁ × Ω₂ => Y x.1)
      = mutualInfo φ Y := by sorry
