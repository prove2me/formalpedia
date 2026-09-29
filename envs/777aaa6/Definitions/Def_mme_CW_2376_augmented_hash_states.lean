-- Prove2me | Definitions.Def_mme_CW_2376_augmented_hash_states
-- name    : mme_CW_2376_augmented_hash_states
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T21:50:49.73482+00:00
-- url     : https://prove2.me/theorems/f55f6c0d-91c7-402d-aba3-185187298267
-- title:
--   Augmented affine hash states retaining a CW marginal edge
-- statement:
--   For a fixed marginal-supported Coppersmith--Winograd edge of word length $N$, consider affine hash states consisting of $N+1$ field weights and one affine offset. The edge is retained using only the first $N$ weights; the final weight is deliberately unused.
--
--   This harmless augmentation makes the exact survival count equal to $|S|p^N$ and avoids a subtraction-dependent reindexing. It also aligns the total parameter-space factor with the normalized collision margin in the outer hashing argument.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), affine outer hashing on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_marginal_hash_retained_edges

namespace MME

noncomputable def cw2376AugmentedHashStatesRetainingAddress
    (m p : ℕ) [NeZero p] (S : Finset ℕ)
    (a : CW2376MarginalSupportedAddress m) :
    Finset ((Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p) := by
  classical
  exact Finset.univ.filter (fun q =>
    a ∈ cw2376MarginalHashRetainedEdges m p S q.2
      (fun j => q.1 j.castSucc))

end MME


