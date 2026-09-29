-- Prove2me | Definitions.Def_Probability_ForkPinningDataProcessing
-- name    : Probability_ForkPinningDataProcessing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:40.425702+00:00
-- url     : https://prove2.me/theorems/31bf90de-3353-4ac5-ba27-8687ed9784b2
-- title:
--   Aether Catalog definitions — Probability_ForkPinningDataProcessing
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ForkPinningDataProcessing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ForkPinningDataProcessing.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
/-
# Coarsening a character can only lose information (data processing), and the
# abelianization is the optimal congruence observable

The fork-pinning criterion says *which* forks a Dirichlet character can pin.  This file makes
the criterion **quantitative**: information about a fork can never be created by post-processing
the observable, so among all abelian characters of the Galois group the abelianization map
`G → G^ab` is the unique optimum:

* `ForkPinning.mutualInfo_comp_le` : the data-processing inequality
  `I(g ∘ X ; Y) ≤ I(X ; Y)` for the uniform measure on a finite space;
* `ForkPinning.mutualInfo_le_of_determines` : a coarser statistic carries less information;
* `ForkPinning.mutualInfo_le_abelianization` : **every** Dirichlet character `f : G →* A`
  satisfies `I(f ; Y) ≤ I(G^ab ; Y)` — no abelian character can beat the abelianization;
* `ForkPinning.abelianization_is_optimal` : the resulting sharp capacity statement, that the
  supremum over abelian characters of the pinned information is attained at `G^ab`.

The proof of the data-processing inequality is a grouped Gibbs argument: writing
`r = P(X = k, Y = b)`, `p = P(X = k)`, `q = P(gX = gk, Y = b)`, `P = P(gX = gk)`, the
elementary inequality `r log r − r log (q p / P) ≥ r − q p / P` is summed over all `(k, b)`;
the right-hand side telescopes to `0` and the left-hand side is exactly `I(X;Y) − I(gX;Y)`.
-/


namespace ForkPinning

open Finset Real

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable {κ κ' β : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype β] [DecidableEq β]

/-! ## Fibres of a post-processed statistic -/







/-! ## The elementary Gibbs term of the data-processing inequality -/


/-! ## The four sum identities -/






/-! ## The data-processing inequality -/



/-- The pointwise information gap of the data-processing inequality: the amount by which the
cell `(k, b)` of the fine joint law fails to be the corresponding coarse cell rescaled. -/
noncomputable def dpiGap (g : κ → κ') (X : Ω → κ) (Y : Ω → β) (k : κ) (b : β) : ℝ :=
  (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))
      - prb (joint X Y) (k, b) * Real.log (prb (joint (fun ω => g (X ω)) Y) (g k, b))
      - prb (joint X Y) (k, b) * Real.log (prb X k)
      + prb (joint X Y) (k, b) * Real.log (prb (fun ω => g (X ω)) (g k)))
    - (prb (joint X Y) (k, b)
      - prb (joint (fun ω => g (X ω)) Y) (g k, b) * prb X k
          / prb (fun ω => g (X ω)) (g k))







/-! ## The abelianization is the optimal congruence observable -/

section Galois

variable {G : Type*} [Group G] [Fintype G] [Nonempty G] [DecidableEq G]
variable {A : Type*} [CommGroup A] [Fintype A] [DecidableEq A]
variable [Fintype (Abelianization G)] [DecidableEq (Abelianization G)]




end Galois

end ForkPinning


