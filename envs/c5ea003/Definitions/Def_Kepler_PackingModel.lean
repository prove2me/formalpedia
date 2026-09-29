-- Prove2me | Definitions.Def_Kepler_PackingModel
-- name    : Kepler_PackingModel
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T01:51:02.826101+00:00
-- url     : https://prove2.me/theorems/fc6e1f5c-eea9-4f24-8ffb-dd8a790886d3
-- title:
--   Packing, finite counts and density comparison
-- statement:
--   This module fixes Euclidean $\mathbb R^3$ and defines a packing to be an arbitrary set of centers whose distinct members are separated by at least $2$, and saturation to mean that every point of space is within distance strictly less than $2$ of some center. It counts centers in open balls by finite natural cardinality, with value zero for infinite intersections and for nonpositive radii. Its finite-container property requires one real constant $c$, allowed to depend on the set and have either sign, such that the origin-centered count is at most $\pi r^3/\sqrt{18}+cr^2$ for every real $r\geq1$. On the closed annulus $2\leq\|v\|\leq63/25$, the local quantity is the sum of $(63-25\|v\|)/13$ over a finite set; the formula is also defined without truncation outside that annulus. The occupied region is the union of open unit balls. The covered fraction is its intersection volume with an observation ball divided by that ball's volume, after converting finite Lebesgue volumes to reals and infinite volumes to zero; division by zero gives zero. Upper density is the real limsup of this fraction at the origin through real radii tending to infinity; upper center density instead divides the count by exactly $r^3$. Real limsup is the infimum of eventual upper bounds, with zero as its empty or unbounded-below default. Optimal density is the real supremum of densities of all packings, with zero as its empty or unbounded-above default. The specified FCC centers are $\sqrt2$ times the integer triples with even coordinate sum. The module also names, without proving, the all-packing finite-container goal; existence of a saturated packing extension with all open-ball counts finite and monotone; the finite-annulus score bound of $12$; the saturated finite-container bound; the implication from the stated count bound to occupied density at most $\pi/\sqrt{18}$; the universal density bound; the FCC packing-and-density equality; and equality of optimal density with that constant. Empty sets, nonpositive observation radii, and the total-function conventions are included; ordinary-limit existence and supremum attainment are not part of the definitions.
--
--   **Source and scope.** Primary §§3–4, pp.6–9; Blueprint packing chapter and §1.2. Local finiteness is a theorem obligation and already has a local Lean proof, not a packing field.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §§3–4, pp.6–9; Blueprint packing chapter and §1.2. Local finiteness is a theorem obligation and already has a local Lean proof, not a packing field.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.LiminfLimsup

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace KeplerMission

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Hales et al. (2017), §3, published PDF p. 6: unit-ball centers. -/
def IsPacking (V : Set Space) : Prop :=
  V.Pairwise (fun u v ↦ 2 ≤ dist u v)

def centersInBall (V : Set Space) (a : Space) (r : ℝ) : Set Space :=
  V ∩ Metric.ball a r

/-- Local finiteness is a separate obligation; `Set.ncard` is zero on infinite sets. -/
noncomputable def centerCount (V : Set Space) (a : Space) (r : ℝ) : ℕ :=
  (centersInBall V a r).ncard

/-- The conclusion of the source theorem, not part of the definition of a packing. -/
def FiniteContainerBound (V : Set Space) : Prop :=
  ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
    (centerCount V 0 r : ℝ) ≤ Real.pi * r ^ 3 / Real.sqrt 18 + c * r ^ 2

/-- Flyspeck `Sphere.saturated`; this property is not required in the final goal. -/
def IsSaturated (V : Set Space) : Prop :=
  ∀ x : Space, ∃ v ∈ V, dist x v < 2

/-- Hales et al. (2017), §4.2, PDF p. 9, the closed annulus in equation (1). -/
def annulus : Set Space :=
  {x | 2 ≤ ‖x‖ ∧ ‖x‖ ≤ (63 : ℝ) / 25}

noncomputable def annulusWeight (t : ℝ) : ℝ :=
  ((63 : ℝ) / 25 - t) / ((63 : ℝ) / 25 - 2)

/-- Finite-set form of equation (1); no geometric or score condition is built into `s`. -/
def LocalAnnulusBound (s : Finset Space) : Prop :=
  ∑ v ∈ s, annulusWeight ‖v‖ ≤ 12

end KeplerMission


set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace KeplerMission

/-- Comparison API only: the occupied open unit balls, as in Lean-Eval. -/
def occupiedRegion (V : Set Space) : Set Space :=
  ⋃ v ∈ V, Metric.ball v 1

noncomputable def coveredFraction (V : Set Space) (a : Space) (r : ℝ) : ℝ :=
  (volume (occupiedRegion V ∩ Metric.ball a r)).toReal /
    (volume (Metric.ball a r)).toReal

noncomputable def upperDensity (V : Set Space) : ℝ :=
  Filter.limsup (coveredFraction V 0) Filter.atTop

noncomputable def upperCenterDensity (V : Set Space) : ℝ :=
  Filter.limsup (fun r : ℝ ↦ (centerCount V 0 r : ℝ) / r ^ 3) Filter.atTop

noncomputable def optimalDensity : ℝ :=
  sSup {d : ℝ | ∃ V : Set Space, IsPacking V ∧ upperDensity V = d}

/-- The set √2 D₃. Its separation and density are claims to prove, not structure fields. -/
def fccCenters : Set Space :=
  {x | ∃ z : Fin 3 → ℤ, (∑ i, z i) % 2 = 0 ∧
    ∀ i, x i = Real.sqrt 2 * (z i : ℝ)}

end KeplerMission


set_option autoImplicit false

namespace KeplerMission

/-- The source's final proposition, with its quantifier order unchanged.
Hales et al. (2017), published PDF p. 6, section 3. -/
def SourceGoal : Prop :=
  ∀ V : Set Space, IsPacking V → ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
    (centerCount V 0 r : ℝ) ≤ Real.pi * r ^ 3 / Real.sqrt 18 + c * r ^ 2

/-- Packing extension and the precise finite-count monotonicity needed to remove
saturation. Source: CPNKNXN, KIUMVTC and kc_imp_the_kc in official Flyspeck. -/
def PackingFoundationContract : Prop :=
  ∀ V : Set Space, IsPacking V →
    ∃ W : Set Space, V ⊆ W ∧ IsPacking W ∧ IsSaturated W ∧
      ∀ a : Space, ∀ r : ℝ,
        (centersInBall V a r).Finite ∧ (centersInBall W a r).Finite ∧
          centerCount V a r ≤ centerCount W a r

/-- The explicit local inequality of Hales et al. (2017), p. 9, equation (1). -/
def AnnulusContract : Prop :=
  ∀ s : Finset Space, IsPacking (s : Set Space) →
    (↑s : Set Space) ⊆ annulus → LocalAnnulusBound s

/-- An intermediate conclusion for saturated packings; saturation is removed
by the foundation contract, never assumed by SourceGoal. -/
def SaturatedContainerContract : Prop :=
  ∀ V : Set Space, IsPacking V → IsSaturated V → FiniteContainerBound V

/-- Derived analytic bridge, not an identification of the two formulations. -/
def CountDensityBridge : Prop :=
  ∀ V : Set Space, IsPacking V → FiniteContainerBound V →
    upperDensity V ≤ Real.pi / Real.sqrt 18

def DensityUpperGoal : Prop :=
  ∀ V : Set Space, IsPacking V → upperDensity V ≤ Real.pi / Real.sqrt 18

/-- Explicit close-packing lower witness, separate from the source upper bound. -/
def FCCWitness : Prop :=
  IsPacking fccCenters ∧ upperDensity fccCenters = Real.pi / Real.sqrt 18

def OptimalDensityGoal : Prop :=
  optimalDensity = Real.pi / Real.sqrt 18

end KeplerMission


