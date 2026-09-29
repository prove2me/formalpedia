-- Prove2me | Definitions.Def_Probability_HadwigerConnected
-- name    : Probability_HadwigerConnected
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:51.204557+00:00
-- url     : https://prove2.me/theorems/b85571e3-a962-48f1-a124-647ffed54666
-- title:
--   Aether Catalog definitions — Probability_HadwigerConnected
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HadwigerConnected`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HadwigerConnected.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_HadwigerInfinite
/-
  Reduction of Hadwiger's Conjecture to Connected Graphs
  =====================================================

  A structural reduction: to prove Hadwiger's conjecture for a parameter `k` it
  suffices to prove it for *connected* graphs.  The two ingredients are

  * a colouring-gluing lemma — a graph is `k`-colourable as soon as each of its
    connected components is (the components are pairwise non-adjacent, so
    independently chosen colourings can be assembled), and
  * minor transfer along induced subgraphs (`isMinor_of_isMinor_induce` from
    `HadwigerCore.lean`) — a `K_{k+1}` minor of a component is a `K_{k+1}` minor
    of the whole graph.

  Main results:

  * `Hadwiger.colorable_of_forall_component_colorable`
  * `Hadwiger.exists_component_not_colorable`
  * `Hadwiger.hadwigerProperty_of_connected` : the reduction.
  * `Hadwiger.hadwigerPropertyGen_of_connected` : the same reduction for the
    finiteness-free form of the conjecture.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): Hadwiger's conjecture should have a "minimal
    counterexample is connected" normalisation, since neither the chromatic
    number nor the minor relation sees the component decomposition.
  Experiment (Experimenter): the gluing lemma is the only delicate point — the
    chosen colouring of a component lives on the subtype `↥c.supp`, so the
    assembled colouring `fun v => F (G.connectedComponentMk v) ⟨v, rfl⟩` is
    dependently typed.  The helper `colorGlue_apply` (proved by `subst`) makes
    the dependency disappear, after which validity is immediate from
    `ConnectedComponent.connectedComponentMk_eq_of_adj`.
  Analysis (Analyst): the reduction needs no finiteness, and it holds verbatim
    for both forms of the conjecture; nothing about `k` is used.  This makes it
    a legitimate preprocessing step for the still-open cases `k ≥ 5`.
  Critique (Critic): the reduction is *not* vacuous — the hypothesis quantifies
    only over connected graphs, a strictly smaller class, and the conclusion is
    the full statement.  Applying it to `k ≤ 2` recovers the theorems already
    proved, which is the sanity check `hadwiger_two_via_connected`.
  Synthesis (PI): combined with `hadwiger_monotone`, Hadwiger's conjecture is
    now known in this development to be antitone in `k` and reducible to
    connected graphs.
  -- !-- Lab Notes -- !--
-/

namespace Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

section Gluing

/-- The colouring assembled from a choice of colouring on each component. -/
private noncomputable def glueColor
    (hcol : ∀ c : G.ConnectedComponent, (G.induce c.supp).Colorable k) (v : V) : Fin k :=
  (hcol (G.connectedComponentMk v)).some ⟨v, rfl⟩



end Gluing





end Hadwiger


