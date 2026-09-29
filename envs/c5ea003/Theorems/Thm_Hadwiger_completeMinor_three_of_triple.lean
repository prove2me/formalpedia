-- Prove2me | Theorems.Thm_Hadwiger_completeMinor_three_of_triple
-- name    : Hadwiger.completeMinor_three_of_triple
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:38:48.235693+00:00
-- url     : https://prove2.me/theorems/4489a0be-90db-456d-9e36-2bc79bee25b9
-- title:
--   Three pairwise disjoint, non-empty, connected and pairwise linked vertex
-- statement:
--   Three pairwise disjoint, non-empty, connected and pairwise linked vertex
--   sets give a `K₃` minor.
--
--   ```lean
--   theorem Hadwiger.completeMinor_three_of_triple{S0 S1 S2 : Set V}
--       (h0 : S0.Nonempty) (h1 : S1.Nonempty) (h2 : S2.Nonempty)
--       (d01 : Disjoint S0 S1) (d02 : Disjoint S0 S2) (d12 : Disjoint S1 S2)
--       (c0 : SetConnected G S0) (c1 : SetConnected G S1) (c2 : SetConnected G S2)
--       (e01 : ∃ x ∈ S0, ∃ y ∈ S1, G.Adj x y)
--       (e02 : ∃ x ∈ S0, ∃ y ∈ S2, G.Adj x y)
--       (e12 : ∃ x ∈ S1, ∃ y ∈ S2, G.Adj x y) :
--       CompleteMinor 3 G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerK3.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerK3.lean#L81

-- Thm stub generated from Probability/HadwigerK3.lean
import Mathlib
import Definitions.Def_Probability_HadwigerCore
import Definitions.Def_Probability_HadwigerK3
/-
  Complete Minors from Branch Families, and `K₃` from a Cycle
  ==========================================================

  This file supplies the *construction* side of the Hadwiger development:

  * `Hadwiger.CompleteMinor n G`               : `Kₙ` is a minor of `G`.
  * `Hadwiger.completeMinor_of_branches`       : a family of pairwise disjoint,
                                                 non-empty, connected, pairwise
                                                 linked vertex sets produces a
                                                 `Kₙ` minor.
  * `Hadwiger.completeMinor_three_of_not_isAcyclic` : **every graph containing a
                                                 cycle has `K₃` as a minor** —
                                                 the contraction half of
                                                 Hadwiger's conjecture for
                                                 `k = 2`.
  * `Hadwiger.completeMinor_two_of_adj`        : an edge gives a `K₂` minor.
  * `Hadwiger.completeMinor_one`               : a vertex gives a `K₁` minor.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): a cycle of any length `n ≥ 3` should contract to a
    triangle by splitting it into the three arcs `{g₀}`, `{g₁}`, `{g₂,…,g_{n-1}}`.
  Experiment (Experimenter): the third arc is realised as the support of the
    walk `(c.take (n-1)).drop 2`, whose vertices are exactly `c.getVert i` for
    `2 ≤ i ≤ n-1` (computed from `take_getVert`, `drop_getVert`, `take_length`,
    `drop_length`).  Connectivity is `setConnected_support`; disjointness comes
    from `IsCycle.getVert_injOn'`, injectivity of `getVert` on `{i ≤ n-1}`.
  Analysis (Analyst): the three linking edges are `g₀g₁`, `g₁g₂` and
    `g_{n-1}g_n = g_{n-1}g₀`, all instances of `adj_getVert_succ`; the corner
    case `n = 3` is *not* special — then the third arc is the singleton `{g₂}`
    and the same three edges do the job.
  Critique (Critic): a shorter "the cycle contains a triangle" argument is
    simply false for `n > 3`; contraction is genuinely needed, which is why the
    arc bookkeeping cannot be avoided.
  Synthesis (PI): combined with `colorable_two_of_isAcyclic` this closes
    Hadwiger's conjecture for `k = 2`.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem Hadwiger.completeMinor_three_of_triple{S0 S1 S2 : Set V}
    (h0 : S0.Nonempty) (h1 : S1.Nonempty) (h2 : S2.Nonempty)
    (d01 : Disjoint S0 S1) (d02 : Disjoint S0 S2) (d12 : Disjoint S1 S2)
    (c0 : SetConnected G S0) (c1 : SetConnected G S1) (c2 : SetConnected G S2)
    (e01 : ∃ x ∈ S0, ∃ y ∈ S1, G.Adj x y)
    (e02 : ∃ x ∈ S0, ∃ y ∈ S2, G.Adj x y)
    (e12 : ∃ x ∈ S1, ∃ y ∈ S2, G.Adj x y) :
    CompleteMinor 3 G := by sorry
