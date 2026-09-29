-- Prove2me | Definitions.Def_Probability_HadwigerK3
-- name    : Probability_HadwigerK3
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:40.277685+00:00
-- url     : https://prove2.me/theorems/5a6b93c2-7e16-4f8e-8b9b-201c7ad08620
-- title:
--   Aether Catalog definitions — Probability_HadwigerK3
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HadwigerK3`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HadwigerK3.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_HadwigerCore
import Definitions.Def_Probability_MinorModel
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

namespace Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `CompleteMinor n G` : the complete graph `Kₙ` is a minor of `G`. -/
def CompleteMinor (n : ℕ) (G : SimpleGraph V) : Prop :=
  MinorTheory.MinorModel.IsMinor (⊤ : SimpleGraph (Fin n)) G





/-! ### A cycle contracts to a triangle -/


end Hadwiger


