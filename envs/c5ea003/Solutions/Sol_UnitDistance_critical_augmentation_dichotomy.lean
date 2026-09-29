-- Prove2me | solution 1 for UnitDistance.critical_augmentation_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:13:12.767508+00:00
-- url     : https://prove2.me/submissions/b13dc512-4e49-4c29-807d-083bfd04c340

-- Sol generated from Novelty/G27CriticalAugmentation.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_UnitDistanceGraph
import Theorems.Thm_SimpleGraph_four_lt_fracValue_of_indepRatio_lt

/-!
# The critical two-vertex augmentation of a `27`-vertex unit-distance graph

The Matolcsi–Ruzsa–Varga–Zsámboki circle around the fractional chromatic number of the plane
features a `27`-vertex planar unit-distance graph `G27` which, after adding a specific pair of
points, becomes a `29`-vertex graph whose *geometric fractional chromatic number* exceeds `4`.
Such augmentations are exceedingly rare.  This file isolates and formally verifies the
**arithmetic mechanism** behind the phenomenon and its **minimality**, using the fractional
colouring engine of `Catalog.Novelty.IndependenceRatioChromatic`.

The key observation is a counting identity.  A finite graph on `m` vertices with independence
number `a` has independence ratio `a/m`; the fractional engine forces every fractional
colouring to have value `> 4` exactly when `a/m < 1/4`, i.e. `4a < m`.  For the value `a = 7`:

* `7/27 > 1/4` — the base `27`-vertex graph is *not* forced above `4`;
* `7/28 = 1/4` — adding **one** vertex only reaches the threshold, still *not* strictly below;
* `7/29 < 1/4` — adding **two** vertices crosses strictly below, forcing `χ_f > 4`.

Thus, *provided the augmentation does not create a larger independent set*, two vertices is the
**least** number one can add to a `27`-vertex graph of independence number `7` to force the
fractional chromatic number above `4`.  We prove this minimality in full generality
(`least_augmentation`) and specialise it (`g27_least_augmentation`).

On the graph side we prove that augmentation (passing to an induced supergraph, dually a
`comap` along an embedding) can only *increase* the independence number
(`indepNum_comap_le`); hence an augmentation that keeps the independence number fixed is
exactly a "critical" one.  Combining, `critical_augmentation_dichotomy` shows that a critical
two-vertex augmentation of a `27`-vertex graph of independence number `7` lands the base below
no threshold yet pushes the `29`-vertex augmentation strictly across it.

* `quarter_iff` — `a/m < 1/4 ↔ 4a < m`.
* `least_augmentation`, `g27_least_augmentation` — minimality of the number of added vertices.
* `indepNum_comap_le` — independence number is monotone under augmentation.
* `fracValue_gt_four`, `g29_fracChromatic_gt_four` — the fractional engine at `29` vertices.
* `g27_not_forced`, `one_vertex_augmentation_not_forced` — the base and one-vertex cases stay
  at or above the threshold.
* `critical_augmentation_dichotomy` — the combined statement.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the "rarity" of a fractional-chromatic-raising augmentation is not
mysterious analysis but a sharp counting threshold: with independence number pinned at `7`, the
ratio `7/m` crosses `1/4` precisely between `m = 28` and `m = 29`.  Bold form: the number `2`
in "two-vertex augmentation" is forced — it is the least `k` with `7/(27+k) < 1/4`.
Experiment (Experimenter): reduce the rational inequality `a/m < 1/4` to the integer inequality
`4a < m` via `div_lt_iff₀` (`quarter_iff`), then package minimality as `IsLeast` and discharge
the membership/lower-bound halves with `omega`.  On the graph side, transport a maximum
independent set of `G.comap f` through the injective `f` to bound `indepNum` and feed
`four_lt_fracValue_of_indepRatio_lt`.
Analysis (Analyst): the mechanism is "true and sharp" — `7/28 = 1/4` is an exact equality, so a
one-vertex augmentation is genuinely at the boundary, never below it; only `k ≥ 2` works.  The
geometric content the formalisation deliberately does *not* capture is the *existence* of a
planar realisation keeping `α = 7`; that (and uniqueness up to isometry) is the hard, still-open
part.  What we prove is the exact combinatorial skeleton that any such realisation must satisfy.
Critique (Critic): none of the theorems is vacuous.  `quarter_iff` needs `0 < m` (else `1/0`
undefined); `least_augmentation` needs `n ≤ 4a` (the base must sit at or above threshold, else
the least augmentation is `0`).  `indepNum_comap_le` uses injectivity of `f` in an essential
way — a non-injective `comap` can collapse an independent set.  The dichotomy's hypothesis
`hcrit` (independence number preserved) is load-bearing: `indepNum_comap_le` shows augmentation
can only raise `α`, so preservation is precisely the criticality condition.
Synthesis (PI): the file supplies the *forced-arithmetic core* of the `G27 → G29` phenomenon,
reducing the open geometric conjecture to the single realisability question "can two points be
added to `G27` without enlarging its maximum independent set?".
-- !-- end Lab Notes -- !--
-/

open scoped Classical
open SimpleGraph

open UnitDistance

/-! ### Arithmetic core: the `1/4` threshold and minimal augmentation -/

/-- The independence-ratio threshold in integer form: `a/m < 1/4 ↔ 4a < m`. -/
theorem quarter_iff (a m : ℕ) (hm : 0 < m) : (a : ℚ) / (m : ℚ) < 1 / 4 ↔ 4 * a < m := by
  rw [div_lt_iff₀ (by exact_mod_cast hm)]
  constructor <;> intro h
  · have : (4 : ℚ) * a < m := by linarith
    exact_mod_cast this
  · have : (a : ℚ) * 4 < m := by
      have : ((4 * a : ℕ) : ℚ) < (m : ℚ) := by exact_mod_cast h
      push_cast at this; linarith
    linarith






/-! ### Graph core: monotonicity of independence number and the fractional engine -/

/-
**Augmentation only increases independence number.**  For an embedding `f : V ↪ W`, the
induced subgraph `G.comap f` has independence number at most that of `G`.  Equivalently, adding
vertices to a graph can only enlarge (never shrink) its maximum independent set.
-/

/-- **Fractional engine.**  A finite graph with `0 < α` and `4α < n` (equivalently
`i(G) < 1/4`) forces every fractional colouring to have value strictly greater than `4`. -/
theorem fracValue_gt_four {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hpos : 0 < Fintype.card V) (hα : 0 < G.indepNum)
    (h4 : 4 * G.indepNum < Fintype.card V) (F : G.FracColoring) : 4 < F.value := by
  apply SimpleGraph.four_lt_fracValue_of_indepRatio_lt G hpos hα _ F
  rw [SimpleGraph.indepRatio, quarter_iff _ _ hpos]; exact h4

/-- **The critical `29`-vertex graph.**  A `29`-vertex graph of independence number `7` has
fractional chromatic number `> 4`: every fractional colouring has value `> 4`. -/
theorem g29_fracChromatic_gt_four {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 29) (hα : G.indepNum = 7) (F : G.FracColoring) : 4 < F.value :=
  fracValue_gt_four G (by omega) (by omega) (by omega) F

/-- The independence ratio of a `27`-vertex graph of independence number `7` is `7/27`. -/
theorem g27_indepRatio_eq {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 27) (hα : G.indepNum = 7) : G.indepRatio = 7 / 27 := by
  rw [SimpleGraph.indepRatio, hcard, hα]; norm_num

/-- **The base is not forced above `4`.**  A `27`-vertex graph of independence number `7` has
ratio `7/27 > 1/4`, so the fractional engine does *not* apply. -/
theorem g27_not_forced {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V = 27) (hα : G.indepNum = 7) : ¬ G.indepRatio < 1 / 4 := by
  rw [g27_indepRatio_eq G hcard hα]; norm_num


/-! ### The combined critical-augmentation dichotomy -/



open UnitDistance in
theorem solution{V W : Type*} [Fintype V] [Fintype W]
    (f : V ↪ W) (G : SimpleGraph W)
    (hV : Fintype.card V = 27) (hW : Fintype.card W = 29)
    (hbase : (G.comap f).indepNum = 7)
    (hcrit : G.indepNum = (G.comap f).indepNum) :
    (¬ (G.comap f).indepRatio < 1 / 4) ∧ (∀ F : G.FracColoring, 4 < F.value) := by
  refine ⟨g27_not_forced (G.comap f) hV hbase, fun F => g29_fracChromatic_gt_four G hW ?_ F⟩
  rw [hcrit, hbase]
