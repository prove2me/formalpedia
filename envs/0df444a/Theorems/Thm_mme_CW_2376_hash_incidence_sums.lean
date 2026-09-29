-- Prove2me | Theorems.Thm_mme_CW_2376_hash_incidence_sums
-- name    : mme_CW_2376_hash_incidence_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:25:48.562671+00:00
-- url     : https://prove2.me/theorems/78fce0e9-198b-429e-9f98-1cbafeea4517
-- title:
--   Exact target survival and bounded target--ambient collision sums
-- statement:
--   Average the augmented affine hash over all $p^{N+2}$ parameter states. If $T$ is the complete exact-profile target family and $C$ is the complete directed target-to-ambient collision family, then the total number of retained target incidences is exactly $T|S|p^N$, while the total number of retained collision incidences is at most $Cp^N$.
--
--   The result follows by double-counting hash-state/edge incidences. Every target edge survives in exactly $|S|p^N$ states, and every fixed distinct pair sharing a mode survives in at most $p^N$ states. Crucially, the ambient member of a collision ranges over the full marginal-supported hypergraph, not merely the exact target profile.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), affine hashing and collision deletion on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_hash_incidence_universes
import Theorems.Thm_mme_CW_2376_target_address_hash_parameter_card
import Theorems.Thm_mme_CW_2376_augmented_pair_collision_card_le
import Theorems.Thm_mme_finset_incidence_double_count

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_CW_2376_hash_incidence_sums
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2)) :
    (∑ q ∈ cw2376AugmentedHashStateUniverse m p,
        (cw2376ExactTargetEdges
          (cw2376RetainedEdgesAtAugmentedState m p S q)).card) =
        (cw2376AllExactTargetEdges m).card * S.card *
          p ^ cw2376ProfileLength m ∧
      (∑ q ∈ cw2376AugmentedHashStateUniverse m p,
        (cw2376TargetAmbientCollisions
          (cw2376RetainedEdgesAtAugmentedState m p S q)).card) ≤
        (cw2376AllTargetAmbientCollisions m).card *
          p ^ cw2376ProfileLength m := by
  sorry
