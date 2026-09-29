-- Prove2me | Definitions.Def_Probability_HadwigerRandomGraph
-- name    : Probability_HadwigerRandomGraph
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:45:31.073992+00:00
-- url     : https://prove2.me/theorems/7cdd4320-3f7a-4868-b492-c4cea978c220
-- title:
--   Aether Catalog definitions — Probability_HadwigerRandomGraph
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HadwigerRandomGraph`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HadwigerRandomGraph.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_ErdosRenyiThreshold
import Definitions.Def_Probability_HadwigerK3
/-
  Minors in the Erdős–Rényi Random Graph
  ======================================

  A bridge between the minor theory developed here and the elementary
  `G(n,p)` model of `ErdosRenyiThreshold.lean`.  The excluded-minor
  characterisation of forests (`HadwigerForest.lean`) says that in the random
  graph the events "has a `K₃` minor" and "is not a forest" are *literally the
  same event*, and the independence computation of the `G(n,p)` model then gives
  an explicit lower bound for its probability.

  Main results:

  * `Hadwiger.RandomGraph.hasK3Minor_eq_hasCycle` : the two events coincide.
  * `Hadwiger.RandomGraph.prob_hasK3Minor_eq_prob_hasCycle`.
  * `Hadwiger.RandomGraph.prob_mono`               : monotonicity of `Prob` in the
                                                     event.
  * `Hadwiger.RandomGraph.pow_three_le_prob_hasK3Minor` : `p³ ≤ P(K₃ ≼ G(n,p))`
                                                     for `n ≥ 3`.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): topological (minor) events should be expressible in
    the elementary configuration model, and the `K₃`-minor event should be
    exactly the complement of acyclicity.
  Experiment (Experimenter): `completeMinor_three_iff_not_isAcyclic` transfers
    verbatim to `graphOf s`; the quantitative bound comes from the fixed triangle
    `{01, 02, 12}`, whose containment probability is `p³` by
    `ErdosRenyi.prob_contains_subset`, together with monotonicity of `Prob`.
  Analysis (Analyst): the bound is tight in order for `p` bounded away from `0`
    and shows the `K₃`-minor event is *not* rare, in contrast with the `K₃`
    *subgraph* event whose expected count is `binom(n,3) p³`.
  Critique (Critic): the lower bound uses only one triangle, so it does not
    capture the `p ~ 1/n` threshold for cycles; sharpening it needs a second
    moment over all cycles, recorded as a future direction.
  Synthesis (PI): the probabilistic and structural halves of the catalog now
    talk to each other through a proved event identity rather than an analogy.
  -- !-- Lab Notes -- !--
-/

namespace Hadwiger.RandomGraph

open SimpleGraph ErdosRenyi Finset
open scoped Classical

/-- The event that the random graph has a `K₃` minor. -/
noncomputable def hasK3Minor (n : ℕ) : Finset (Finset (Edge n)) :=
  Finset.univ.filter (fun s => CompleteMinor 3 (graphOf s))

/-- The event that the random graph contains a cycle. -/
noncomputable def hasCycle (n : ℕ) : Finset (Finset (Edge n)) :=
  Finset.univ.filter (fun s => ¬ (graphOf s).IsAcyclic)





end Hadwiger.RandomGraph


