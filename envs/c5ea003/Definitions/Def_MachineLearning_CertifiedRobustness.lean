-- Prove2me | Definitions.Def_MachineLearning_CertifiedRobustness
-- name    : MachineLearning_CertifiedRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:04.422541+00:00
-- url     : https://prove2.me/theorems/56971c25-6c08-49e5-9ea6-4d7ba88e816b
-- title:
--   Aether Catalog definitions — MachineLearning_CertifiedRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CertifiedRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CertifiedRobustness.lean by skeleton subtraction
import Mathlib

/-!
# Certified robustness and a finite cellular sheaf counterexample

This file isolates a precise contrarian test of the proposed principle.  The
cohomology model is the degree-one cellular cohomology of the constant real
sheaf on the graph consisting of two weight charts and their overlap.  Its
first cohomology vanishes, but this topological fact alone does not constrain
a classifier's decision margin.  A threshold classifier supplies a certified
counterexample.  We also prove a corrected analytic theorem: a positive margin
together with a local Lipschitz estimate gives an explicit `L∞` certificate.
-/

namespace CertifiedAdversarialRobustness

/-- The decision associated to a real-valued score, with zero assigned to the
negative class. -/
noncomputable def decision {X : Type*} (score : X → ℝ) (x : X) : Bool := decide (0 < score x)

/-- A strict-radius robustness certificate in an arbitrary distance model. -/
def CertifiedAt {X : Type*} (dist : X → X → ℝ) (score : X → ℝ)
    (x : X) (radius : ℝ) : Prop :=
  ∀ y, dist x y < radius → decision score y = decision score x

/-- A concrete `L∞` distance on finite-dimensional real input spaces. -/
noncomputable def linfDist {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ‖x - y‖

/-- The local vulnerability stalk at `(x,r)`: its elements are adversarial
examples lying strictly inside the `L∞` ball. -/
def VulnerabilityStalk {n : ℕ} (score : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (radius : ℝ) :=
  {y : Fin n → ℝ // linfDist x y < radius ∧ decision score y ≠ decision score x}


/-! ## A two-chart cellular sheaf

A section over the two vertices is a pair `(a,b)`.  Its Čech/cellular
coboundary on their oriented overlap is `b-a`.  Degree-one cohomology vanishes
when every overlap cochain is such a coboundary.
-/

/-- Degree-zero coboundary for the constant sheaf on one edge. -/
def edgeCoboundary (s : ℝ × ℝ) : ℝ := s.2 - s.1

/-- Vanishing first cohomology of the two-chart constant cellular sheaf. -/
def EdgeH1Vanishing : Prop := Function.Surjective edgeCoboundary


/-- On the real line, the absolute-value metric is the one-dimensional
`L∞` metric. -/
def realLinfDist (x y : ℝ) : ℝ := |x - y|




/-! ## Corrected positive statement

Topology can organize local data, but a numerical certificate requires an
analytic bridge.  The next result gives that bridge without assuming any
cohomology: positive score margin and a local Lipschitz bound imply robustness.
-/


end CertifiedAdversarialRobustness


