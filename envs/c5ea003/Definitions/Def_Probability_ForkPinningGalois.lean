-- Prove2me | Definitions.Def_Probability_ForkPinningGalois
-- name    : Probability_ForkPinningGalois
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:00.637673+00:00
-- url     : https://prove2.me/theorems/ace4b23f-ebd8-4bec-89fd-a2cf9a0d798e
-- title:
--   Aether Catalog definitions — Probability_ForkPinningGalois
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ForkPinningGalois`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ForkPinningGalois.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
/-
# The fork-pinning criterion on three Galois groups: C₃, S₃, S₄

Model.  By Chebotarev, a random prime (unramified, in the natural density sense) produces a
uniformly random Frobenius element of the Galois group `G` of the splitting field, the splitting
type of the defining polynomial being the cycle type of that element on the roots.  Congruence
information about the prime is exactly the information visible through *abelian* characters of
`G`, i.e. through the abelianization `G^ab`.  Everything below is a theorem about the uniform
measure on the finite group `G`.

Main results.

* `ForkPinning.determines_abelianization_of_hom` — **the criterion**: if a fork is determined by
  *some* abelian character of `G`, it is determined by the abelianization map.  With
  `pinned_iff_determines` this says: a fork is congruence-pinned iff it factors through `G^ab`.
* `ForkPinning.comm_fork_pinned` — for an **abelian** Galois group *every* fork is pinned at
  100% of its entropy.
* `ForkPinning.cyclicCubic_fork_mutualInfo` — the cyclic cubic ([1,1,1] fork, `G = C₃`):
  `I = H(fork) = log 3 − (2/3) log 2` (= 0.9183 bits), matching the measured `0.9182`.
* `ForkPinning.S3_fork_mutualInfo` — the `S₃` cubic ([1,1,1] fork):
  `I = (4/3) log 2 + (1/2) log 3 − (5/6) log 5` (= 0.1909 bits), matching the measured `0.1906`;
  and `S3_fork_not_pinned`, `S3_mutualInfo_lt_entropy` : the pinning is strictly partial —
  only the quadratic (sign) character is seen.
* `ForkPinning.S4_hasRoot_mutualInfo` — the `S₄` quartic (has-a-root fork):
  `I = (3/2) log 2 − (5/8) log 5` (= 0.0488 bits), matching the measured `0.0483`.
* `ForkPinning.mutualInfo_flat_on_commutator` — **every within-face fork is flat**: on the
  commutator subgroup (the even face) every abelian character is constant, so its mutual
  information with an arbitrary fork is exactly `0`.
-/

open scoped commutatorElement

namespace ForkPinning

open Finset Real

/-! ## The criterion: pinned ⟺ factors through the abelianization -/

section Criterion

variable {G : Type*} [Group G] [Fintype G] [Nonempty G]
variable {A β : Type*} [CommGroup A] [Fintype β] [DecidableEq β]






end Criterion

/-! ## Within-face flatness -/

section Face

variable {G : Type*} [Group G] {A β : Type*} [CommGroup A] [Fintype A] [DecidableEq A]
  [Fintype β] [DecidableEq β]


end Face

/-! ## Numerical toolkit -/

section Toolkit

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]




end Toolkit

/-! ### Logarithms of the small integers that occur -/





/-! ## (1) The cyclic cubic field: `G = C₃`, the fork is pinned at 100% -/

section CyclicCubic

/-- The `[1,1,1]` fork of a cyclic cubic field: the Frobenius is trivial. -/
def forkC3 (g : ZMod 3) : Bool := decide (g = 0)








end CyclicCubic

/-! ## (2) The `S₃` cubic: only the sign is pinned -/

section S3

/-- The sign character — the abelianization of `Sₙ` for `n = 3, 4`. -/
def signBool {n : ℕ} (σ : Equiv.Perm (Fin n)) : Bool := decide (Equiv.Perm.sign σ = 1)

/-- Splitting type `[1,1,1]`: the Frobenius fixes all three roots. -/
def forkSplit3 (σ : Equiv.Perm (Fin 3)) : Bool := decide (σ = 1)















end S3

/-! ## (3) The `S₄` quartic: only the sign is pinned -/

section S4

/-- The quartic has a root mod `p`: the Frobenius fixes one of the four roots. -/
def forkHasRoot (σ : Equiv.Perm (Fin 4)) : Bool := decide (∃ i, σ i = i)
















end S4

/-! ## Comparison: abelian closure pins strictly more than the `S₃` closure -/


/-! ## A checkable form of the criterion, and "no character pins it" theorems -/

section CommutatorForm

variable {G : Type*} [Group G] {β : Type*}


variable [Fintype G] [Nonempty G] [Fintype β] [DecidableEq β]



end CommutatorForm

/-! ## Capacity of the sign character -/



/-! ## The two non-abelian forks are pinned by *no* Dirichlet character -/






end ForkPinning


