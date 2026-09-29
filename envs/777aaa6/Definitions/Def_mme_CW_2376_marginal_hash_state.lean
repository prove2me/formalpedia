-- Prove2me | Definitions.Def_mme_CW_2376_marginal_hash_state
-- name    : mme_CW_2376_marginal_hash_state
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T20:13:56.360377+00:00
-- url     : https://prove2.me/theorems/cdd9f4b4-2d2e-4657-99c7-6fff959d9c8c
-- title:
--   Hash-retained target and ambient edges for outer CW pruning
-- statement:
--   For a retained subset $E$ of the full marginal-supported Coppersmith--Winograd hypergraph, this module defines three pieces of the finite pruning state. First, vertex closure says that every supported mixed edge assembled from retained vertices is also in $E$. Second, $T(E)$ is the subset with the dominant equation-(13) joint profile. Third, $C(T,E)$ is the set of directed target--ambient collision pairs.
--
--   These definitions encode the sound order of the source argument on journal pp. 267--269. The affine hash and progression-free set establish closure for the full marginal hypergraph; only afterward is the dominant target profile selected. Counting directed collisions from target edges suffices to isolate an induced target family and avoids charging irrelevant collisions between two non-target edges.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13), affine hashing, and collision deletion on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Finset.Prod
import Definitions.Def_mme_CW_2376_marginal_support_hypergraph

namespace MME

def CW2376MarginalVertexClosed {m : ℕ}
    (E : Finset (CW2376MarginalSupportedAddress m)) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, ∀ z ∈ E,
    CW2376CoordinatewiseSupported
      (cw2376MixedAddress x.1 y.1 z.1) →
    ∃ e ∈ E, e.1 = cw2376MixedAddress x.1 y.1 z.1

noncomputable def cw2376ExactTargetEdges {m : ℕ}
    (E : Finset (CW2376MarginalSupportedAddress m)) :
    Finset (CW2376MarginalSupportedAddress m) := by
  classical
  exact E.filter CW2376HasExactJointProfile

noncomputable def cw2376TargetAmbientCollisions {m : ℕ}
    (E : Finset (CW2376MarginalSupportedAddress m)) :
    Finset (CW2376MarginalSupportedAddress m ×
      CW2376MarginalSupportedAddress m) := by
  classical
  exact (cw2376ExactTargetEdges E ×ˢ E).filter (fun p =>
    p.1 ≠ p.2 ∧ ∃ i : Fin 3, p.1.1 i = p.2.1 i)

end MME


