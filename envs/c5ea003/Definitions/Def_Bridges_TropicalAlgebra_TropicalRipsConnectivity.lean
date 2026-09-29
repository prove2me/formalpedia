-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_TropicalRipsConnectivity
-- name    : Bridges_TropicalAlgebra_TropicalRipsConnectivity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:44.580311+00:00
-- url     : https://prove2.me/theorems/ffb5df74-6adb-49ee-b317-f9244cf48894
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_TropicalRipsConnectivity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.TropicalRipsConnectivity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/TropicalRipsConnectivity.lean by skeleton subtraction
import Mathlib
/-
  # A Functorial Tropical Lower Bound for Rips Connectivity
  ## via Valuation-Depth Sublevel Graphs

  Bridge: connects **metric filtrations / Vietoris–Rips graphs**
  (`Applications/PoincareData/MetricFiltration.lean`) ↔ **tropical (max-plus) valuation
  algebra** (`Bridges/CategoricalTropicalUltrametric.lean`) ↔ **ultrametric / valuation
  depth** (`Computation/PadicValuationDepth.lean`).

  ## Core principle

  In a *general* pseudometric space, two points may become path-connected in the Rips
  graph at scale `ε` even when their distance is much larger than `ε`: connectivity is
  governed by the **bottleneck (tropical) path distance** `min over paths of max edge`,
  which can be far below the true distance. This is the "Archimedean leak": a chain of
  short edges spans a long distance.

  Over an **ultrametric** (= non-Archimedean / valuation) space the strong triangle
  inequality `dist x z ≤ max (dist x y) (dist y z)` plugs this leak completely: the
  bottleneck path distance **equals** the metric distance, so

      `Reachable_ε x y  ↔  dist x y ≤ ε`.

  Hence the **connectivity threshold** `connThreshold x y := dist x y` is the exact
  (tight, tropically certified) scale at which `x` and `y` merge, and — being a metric
  distance on an ultrametric space — it *itself* satisfies the tropical/max inequality.
  This is the "functorial tropical lower bound": the connectivity-threshold functor lands
  in the tropical (max) semiring, and `dist x y` is a *certified lower bound* on any scale
  that can connect `x` to `y`.

  ## Main results

  * `ripsGraph`                       — Rips 1-skeleton at scale `ε` (re-stated, self-contained)
  * `ripsGraph_mono`                  — filtration monotonicity
  * `reachable_mono`                  — functoriality: reachability is monotone in `ε`
  * `dist_le_of_walk_length`          — general (Archimedean) bound: `dist ≤ length · ε`
  * `reachable_dist_le`               — **ultrametric collapse**: reachable ⇒ `dist ≤ ε`
  * `reachable_iff`                   — `Reachable_ε x y ↔ dist x y ≤ ε`
  * `reachableSet_eq_closedBall`      — connectivity classes are closed balls
  * `connThreshold_ultra`             — the threshold functor is tropical (max-subadditive)
  * `rips_connectivity_lower_bound`   — `dist x y` certifies a lower bound on connecting scale

  -- !-- Lab Notes -- !--
  HYPOTHESIS (H1): In an ultrametric space the Rips reachability relation collapses to a
  single sublevel test `dist ≤ ε`.  CONFIRMED below (`reachable_iff`).
  HYPOTHESIS (H2): The connectivity threshold inherits the tropical max-inequality.
  CONFIRMED (`connThreshold_ultra`) — it is literally the strong triangle inequality.
  FAILURE ANALYSIS: the naive statement `Reachable ⇒ dist ≤ ε` is FALSE without `0 ≤ ε`
  (the reflexive walk `x = x` is always reachable yet forces `dist x x = 0 ≤ ε`), and
  FALSE without ultrametricity (chains of short edges, see `dist_le_of_walk_length` which
  is the best general bound). Both hypotheses are therefore load-bearing.
  -- !--
-/

open Function Metric

noncomputable section

namespace TropicalRipsConnectivity

universe u
variable {α : Type u}

/-! ## §1. The Rips graph (self-contained re-statement) -/

/-- The **Rips graph** (Vietoris–Rips 1-skeleton) at scale `ε`: distinct points are
    adjacent iff within distance `ε`.  Re-stated from
    `Applications/PoincareData/MetricFiltration.lean` so this file builds standalone. -/
def ripsGraph (α : Type u) [PseudoMetricSpace α] (ε : ℝ) : SimpleGraph α where
  Adj x y := x ≠ y ∧ dist x y ≤ ε
  symm x y h := ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩
  loopless := ⟨fun x h => h.1 rfl⟩

variable [PseudoMetricSpace α]




/-! ## §2. The general (Archimedean) bound -/


/-! ## §3. The ultrametric collapse -/

variable [IsUltrametricDist α]




/-! ## §4. The tropical connectivity-threshold functor -/

/-- The **connectivity threshold**: the exact scale at which `x` and `y` merge in the
    Rips filtration.  Over an ultrametric space this equals the distance. -/
def connThreshold (x y : α) : ℝ := dist x y



end TropicalRipsConnectivity


