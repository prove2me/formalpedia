-- Prove2me | Theorems.Thm_Shamir1979_hierarchical_threshold
-- name    : Shamir1979.hierarchical_threshold
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-29T07:52:59.645347+00:00
-- url     : https://prove2.me/theorems/60804a9a-78aa-4ace-aff7-9d11b8e59ab7
-- title:
--   Section 2, property (4) — hierarchical allocation of polynomial shares
-- statement:
--   Allocate any finite sets of participant locations to people, allowing a person to hold several polynomial evaluations. A finite coalition can reconstruct whenever the union of the locations it holds contains at least $k$ distinct locations. If that union has fewer than $k$ locations, its joint share transcript has the same uniform distribution for every secret. Overlapping holdings are counted once, so giving the same evaluation to two people does not create an additional independent share. The paper's hierarchical example is obtained by allocating three, two, or one distinct locations to its three participant classes.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §2, p. 613, useful property (4)

import Definitions.Def_Shamir1979_Model

open scoped BigOperators
universe u

namespace Shamir1979

theorem hierarchical_threshold (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p)
    {A : Type u} (holdings : A → Finset (Fin n)) (coalition : Finset A) :
    (k ≤ (heldLocations holdings coalition).card →
      ∀ (secret : ZMod p) (coins : Coins p k),
        recover (heldLocations holdings coalition)
          (observe (heldLocations holdings coalition) secret coins) = secret) ∧
    ((heldLocations holdings coalition).card < k →
      ∀ (secret : ZMod p) (values : Observation p (heldLocations holdings coalition)),
        observationProbability (k := k) (heldLocations holdings coalition) secret values =
          (1 : Rat) / (p : Rat) ^ (heldLocations holdings coalition).card) := by sorry

end Shamir1979
