-- Prove2me | Definitions.Def_Probability_HadwigerBipartite
-- name    : Probability_HadwigerBipartite
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:48.63919+00:00
-- url     : https://prove2.me/theorems/139fb32a-84d7-45c4-ade1-7f89ab3fc25d
-- title:
--   Aether Catalog definitions — Probability_HadwigerBipartite
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HadwigerBipartite`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HadwigerBipartite.lean by skeleton subtraction
import Mathlib
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

namespace Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Swapping the two colours of `Fin 2`. -/
def flip2 (a : Fin 2) : Fin 2 := a + 1






end Hadwiger


