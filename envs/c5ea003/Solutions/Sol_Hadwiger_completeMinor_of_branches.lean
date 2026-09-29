-- Prove2me | solution 1 for Hadwiger.completeMinor_of_branches
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:23:14.15693+00:00
-- url     : https://prove2.me/submissions/b69e0233-b99d-4c56-9d3b-010ff8279fbf

-- Sol generated from Probability/HadwigerK3.lean
import Mathlib
import Definitions.Def_Probability_HadwigerCore
import Definitions.Def_Probability_HadwigerK3
import Definitions.Def_Probability_MinorModel
import Theorems.Thm_Hadwiger_walkMinor_iff_isMinor
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






/-! ### A cycle contracts to a triangle -/



open Hadwiger in
theorem solution{n : ℕ} (b : Fin n → Set V)
    (hne : ∀ i, (b i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (b i) (b j))
    (hconn : ∀ i, SetConnected G (b i))
    (hedge : ∀ i j, i ≠ j → ∃ x ∈ b i, ∃ y ∈ b j, G.Adj x y) :
    CompleteMinor n G := by
  refine walkMinor_iff_isMinor.mp ⟨⟨b, hne, fun i j hij => hdisj i j hij, hconn, ?_⟩⟩
  intro i j hij
  exact hedge i j (by simpa using hij.ne)
