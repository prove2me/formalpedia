-- Prove2me | Theorems.Thm_Hadwiger_colorable_two_of_isAcyclic
-- name    : Hadwiger.colorable_two_of_isAcyclic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:41:45.775819+00:00
-- url     : https://prove2.me/theorems/f3e54145-b278-4aa2-b0f0-f5799906b937
-- title:
--   Forests are bipartite.
-- statement:
--   **Forests are bipartite.**  Every finite acyclic graph is `2`-colourable.
--
--   ```lean
--   theorem Hadwiger.colorable_two_of_isAcyclic[Finite V] {G : SimpleGraph V}
--       (h : G.IsAcyclic) : G.Colorable 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerBipartite.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerBipartite.lean#L66

-- Thm stub generated from Probability/HadwigerBipartite.lean
import Mathlib
import Definitions.Def_Probability_HadwigerBipartite
/-
  Forests are Bipartite: the Colouring Half of Hadwiger's Conjecture for k = 2
  ===========================================================================

  Hadwiger's conjecture for `k = 2` says that a graph needing three colours has
  `K₃` as a minor; contrapositively, a graph with **no** `K₃` minor — that is, a
  forest — is `2`-colourable.  Mathlib knows that bipartite graphs have no odd
  cycles only as a `TODO`, so this file proves the colouring statement from
  scratch:

  * `Hadwiger.colorable_two_of_isAcyclic` : every finite acyclic graph is
                                            `2`-colourable.

  The proof is a genuine induction on the number of edges using the fact
  (`SimpleGraph.isAcyclic_iff_forall_adj_isBridge`) that *every* edge of a forest
  is a bridge: deleting an edge `uv` splits `u` from `v`, so a `2`-colouring of
  the smaller forest can be repaired by flipping the colours on the whole
  connected component of `v`.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): forests are 2-colourable, and the cleanest formal
    route avoids "leaf extraction" (which needs a degree count and a change of
    vertex type) in favour of edge deletion at constant vertex type.
  Experiment (Experimenter): deleting an arbitrary edge `uv` of an acyclic `G`
    leaves an acyclic `G'` with strictly fewer edges; the inductive colouring `C`
    of `G'` may accidentally satisfy `C u = C v`, so the repair step flips the
    colour on `{x | G'.Reachable v x}`.  Flipping on a whole component preserves
    properness because both endpoints of a `G'`-edge are reachable from `v` or
    neither is.
  Analysis (Analyst): the bridge property `¬ G'.Reachable u v` is exactly what
    makes the flip fix the offending edge without breaking anything else — this
    is where acyclicity enters, and it is the only place.
  Critique (Critic): the induction is on `Set.ncard G.edgeSet`, which needs
    finiteness of `V`; the statement is therefore given for `[Finite V]`.  For
    infinite forests 2-colourability still holds (De Bruijn–Erdős) but that is a
    compactness argument outside the present scope.
  Synthesis (PI): together with `HadwigerK3.lean` (cycle ⇒ `K₃` minor) this
    yields Hadwiger's conjecture for `k = 2`.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem Hadwiger.colorable_two_of_isAcyclic[Finite V] {G : SimpleGraph V}
    (h : G.IsAcyclic) : G.Colorable 2 := by sorry
