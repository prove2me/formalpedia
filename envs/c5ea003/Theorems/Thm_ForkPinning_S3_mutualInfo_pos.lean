-- Prove2me | Theorems.Thm_ForkPinning_S3_mutualInfo_pos
-- name    : ForkPinning.S3_mutualInfo_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:58.338314+00:00
-- url     : https://prove2.me/theorems/dbc6b912-59d7-4887-ac69-d6617a718680
-- title:
--   …but it is strictly positive: the sign *is* pinned (`2⁸·3³ = 6912 > 3125 = 5⁵`).
-- statement:
--   …but it is strictly positive: the sign *is* pinned (`2⁸·3³ = 6912 > 3125 = 5⁵`).
--
--   ```lean
--   theorem ForkPinning.S3_mutualInfo_pos:
--       0 < mutualInfo (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningGalois.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningGalois.lean#L297

-- Thm stub generated from Probability/ForkPinningGalois.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
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

open ForkPinning

open Finset Real

/-! ## The criterion: pinned ⟺ factors through the abelianization -/


variable {G : Type*} [Group G] [Fintype G] [Nonempty G]
variable {A β : Type*} [CommGroup A] [Fintype β] [DecidableEq β]







/-! ## Within-face flatness -/


variable {G : Type*} [Group G] {A β : Type*} [CommGroup A] [Fintype A] [DecidableEq A]
  [Fintype β] [DecidableEq β]



/-! ## Numerical toolkit -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]





/-! ### Logarithms of the small integers that occur -/





/-! ## (1) The cyclic cubic field: `G = C₃`, the fork is pinned at 100% -/











/-! ## (2) The `S₃` cubic: only the sign is pinned -/

theorem ForkPinning.S3_mutualInfo_pos:
    0 < mutualInfo (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3 := by sorry
