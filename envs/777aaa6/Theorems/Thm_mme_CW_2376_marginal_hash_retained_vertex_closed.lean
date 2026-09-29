-- Prove2me | Theorems.Thm_mme_CW_2376_marginal_hash_retained_vertex_closed
-- name    : mme_CW_2376_marginal_hash_retained_vertex_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:10.255944+00:00
-- url     : https://prove2.me/theorems/63e051f8-a48f-4d81-896b-e054605b69e1
-- title:
--   Progression-free CW hashing is closed on the full marginal hypergraph
-- statement:
--   Let $p$ be odd and let $S$ be a three-term-progression-free set of labels contained in the lower half of the modulus. For any affine CW hash parameters, the retained subset of the full marginal-supported address hypergraph is vertex closed: whenever three retained mode words form a coordinatewise-supported mixed address, that mixed address is also retained.
--
--   This is the full inducedness bridge required by the source argument. It applies to all supported mixed profiles, not only to the optimized exact joint profile selected later for the target count.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), modular affine hashes and three-progression-free pruning on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_marginal_hash_retained_edges
import Theorems.Thm_mme_CW_2376_modular_hash_AP_identity
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

open MME

theorem mme_CW_2376_marginal_hash_retained_vertex_closed
    (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (cw2376ProfileLength m) → ZMod p)
    (hpodd : Odd p)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
    CW2376MarginalVertexClosed
      (cw2376MarginalHashRetainedEdges m p S b0 w) := by
  sorry
