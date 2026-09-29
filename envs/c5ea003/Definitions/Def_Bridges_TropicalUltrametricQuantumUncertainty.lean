-- Prove2me | Definitions.Def_Bridges_TropicalUltrametricQuantumUncertainty
-- name    : Bridges_TropicalUltrametricQuantumUncertainty
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T22:55:58.577687+00:00
-- url     : https://prove2.me/theorems/117b6081-1429-404c-b3a1-5b8466658d67
-- title:
--   Aether Catalog definitions — Bridges_TropicalUltrametricQuantumUncertainty
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalUltrametricQuantumUncertainty`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalUltrametricQuantumUncertainty.lean by skeleton subtraction
import Mathlib
/-
# Functorial Entropic Uncertainty via Tropical–Ultrametric Quantum Measurement Skeletons

This file formalizes a reusable *measurement skeleton* framework connecting:
- **Quantum information**: finite measurement overlap matrices and outcome distributions
- **Tropical/valuation geometry**: tropicalized overlap profiles via `-log`
- **Ultrametric analysis**: valuation radii from tropical/ultrametric transfer
- **Cryptographic entropy extraction**: min-entropy and collision-entropy lower bounds

The core insight is that quantum measurement incompatibility, encoded in an overlap matrix,
can be pushed through a tropical interface to produce certified entropy lower bounds
without direct operator analysis.
-/

open Finset BigOperators Real

noncomputable section

/-! ## Section 1: Clipped Logarithm

We define a regularized negative logarithm that avoids the singularity at zero
by clipping the argument below at `exp(-1)`. This produces a total, well-behaved
function suitable for tropical profile extraction.
-/

/-- `clippedLog x = -log(max(x, e⁻¹))`. A certified robust lower-envelope
regularization of `-log x` that is total and nonneg on `[0,1]`.
Bridge: connects tropical valuation geometry to ultrametric analysis. -/
def clippedLog (x : ℝ) : ℝ := - Real.log (max x (Real.exp (-1)))









/-! ## Section 2: Finite Measurement Overlap Matrix

The overlap matrix encodes `|⟨eᵢ, fⱼ⟩|²` for two quantum measurement bases.
We work abstractly with any finite matrix of values in `[0,1]`.
-/

/-- A finite measurement overlap matrix with entries in `[0,1]`.
Bridge: connects quantum measurement overlap to tropical valuation geometry. -/
structure FiniteMeasurementOverlap (ι : Type*) [Fintype ι] where
  ov : ι → ι → ℝ
  nonneg : ∀ i j, 0 ≤ ov i j
  le_one : ∀ i j, ov i j ≤ 1

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Symmetry predicate for overlap matrices.
Bridge: connects symmetric ultrametric measurement structures. -/
def FiniteMeasurementOverlap.IsSymmetric (M : FiniteMeasurementOverlap ι) : Prop :=
  ∀ i j, M.ov i j = M.ov j i

/-- The maximum overlap across all index pairs.
Bridge: connects quantum measurement overlap to tropical valuation geometry.
Computing this requires scanning all `|ι|²` entries: O((Fintype.card ι)²). -/
def FiniteMeasurementOverlap.maxOverlap (M : FiniteMeasurementOverlap ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i =>
    Finset.univ.sup' Finset.univ_nonempty (fun j => M.ov i j))




/-! ## Section 3: Tropical Overlap Profile and Valuation Radius

We tropicalize the overlap matrix by applying `clippedLog`, producing
a "cost" matrix in the max-plus / tropical sense.
-/

/-- The tropicalized overlap profile: `clippedLog(ov(i,j))` for each pair.
Bridge: connects quantum measurement overlap to tropical valuation geometry. -/
def tropicalOverlapProfileClipped
    (M : FiniteMeasurementOverlap ι) : ι → ι → ℝ :=
  fun i j => clippedLog (M.ov i j)


/-- The valuation radius: `clippedLog(maxOverlap)`.
This is the global entropy floor extracted from the overlap matrix.
Bridge: connects tropical valuation geometry to ultrametric analysis. -/
def valuationRadius (M : FiniteMeasurementOverlap ι) : ℝ :=
  clippedLog (M.maxOverlap)





/-! ## Section 4: Probability Vectors and Entropy Surrogates

We define finite probability distributions and their entropy measures.
-/

/-- A predicate for finite probability vectors: nonneg entries summing to 1. -/
def IsFiniteProbVec (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1


/-
The sup of a probability vector is positive (since the sum is 1).
-/

/-- The collision energy (Rényi-2 collision probability): `∑ᵢ pᵢ²`.
Bridge: connects Rényi-2 uncertainty to post-quantum extraction. -/
def collisionEnergy (p : ι → ℝ) : ℝ := ∑ i, (p i) ^ 2



/-- The min-entropy lower surrogate: `-log(max pᵢ)`.
Bridge: connects quantum information to certified entropy witnesses. -/
def minEntropyLowerSurrogate (p : ι → ℝ) : ℝ :=
  - Real.log (Finset.univ.sup' Finset.univ_nonempty p)

/-- The collision-entropy lower surrogate: `-log(∑ pᵢ²)`.
Bridge: connects Rényi-2 uncertainty to post-quantum extraction. -/
def collisionEntropyLowerSurrogate (p : ι → ℝ) : ℝ :=
  - Real.log (collisionEnergy p)

/-
Bridge: connects quantum information to certified entropy witnesses.
Min-entropy lower surrogate is at least `clippedLog c` when `p` is a probability
vector with all entries bounded by `c ≤ 1`.
Proof: sup p ≤ c ≤ max c exp(-1), sup p > 0, so -log(sup p) ≥ -log(max c exp(-1)).
-/

/-
Bridge: connects Rényi-2 uncertainty to post-quantum extraction.
Collision entropy lower surrogate is at least `clippedLog c` when collision
energy is positive and bounded by `c ≤ 1`.
-/

/-! ## Section 5: Collision Energy Lower Bound from Cardinality

A uniform distribution over `|ι|` outcomes has collision energy `1/|ι|`,
which is the minimum possible. This gives an entropy ceiling of `log |ι|`.
-/

/-
Bridge: connects quantum information to post_quantum_security.
The collision energy of a probability vector is at least `1/|ι|` (Cauchy-Schwarz).
This gives a lower bound on collision probability from the outcome space size.
-/

/-
Collision energy of a probability vector is strictly positive.
-/

/-
Bridge: connects Rényi-2 quantum uncertainty to post_quantum_security.
The certified collision entropy is bounded above by `log |ι|`, i.e., O(log |ι|).
This gives a computationally meaningful entropy ceiling for any finite measurement.
-/

/-! ## Section 6: Quantum Measurement Skeleton

The main structure combining overlap data with outcome distributions.
-/

/-- A quantum measurement skeleton: a pair of outcome distributions
over a shared finite index type, together with an overlap matrix.
Bridge: connects quantum measurement overlap to tropical valuation geometry. -/
structure QuantumMeasurementSkeleton (ι : Type*) [Fintype ι] where
  overlap : FiniteMeasurementOverlap ι
  pA : ι → ℝ
  pB : ι → ℝ
  pA_prob : IsFiniteProbVec pA
  pB_prob : IsFiniteProbVec pB

/-- The transferred min-entropy bound from the measurement skeleton.
Bridge: connects quantum measurement overlap to tropical valuation geometry. -/
def transferredMinEntropyBound
    (Q : QuantumMeasurementSkeleton ι) : ℝ :=
  valuationRadius Q.overlap





/-! ## Section 7: Two-Measurement Uncertainty Sum

The Maassen–Uffink skeleton: combined entropy from both measurements. -/

/-
Bridge: connects quantum measurement overlap to tropical hash collision bound.
The sum of min-entropies from both measurements is at least the valuation radius,
when each outcome probability is bounded by `√(maxOverlap)` and maxOverlap ≤ 1.

This is the measurement-skeleton shadow of the Maassen–Uffink inequality.
-/

/-! ## Section 8: Functorial Transfer

Morphisms between measurement skeletons preserve entropy bounds. -/

/-- A morphism of quantum measurement skeletons: a map on index types
that decreases overlaps (i.e., increases incompatibility).
Bridge: connects quantum information to tropical valuation geometry functorially. -/
structure MeasurementSkeletonHom
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : QuantumMeasurementSkeleton ι) (B : QuantumMeasurementSkeleton κ) where
  toFun : ι → κ
  overlap_monotone : ∀ i j, B.overlap.ov (toFun i) (toFun j) ≤ A.overlap.ov i j

/-
Bridge: connects quantum information to tropical valuation geometry.
Overlap-decreasing morphisms increase the valuation radius:
entropy lower bounds are functorial. This is the key "field-opening" result.
-/

/-! ## Section 9: Tropical–Ultrametric Transfer Structure -/



/-! ## Section 10: Existence Witnesses and Cryptographic Corollaries -/




/-! ## Section 11: Maassen–Uffink Skeleton (Clipped) -/



/-! ## Section 12: Lipschitz Certified Robustness Shadow

The overlap radius can be interpreted as an adversarial margin:
perturbations that reduce overlap increase the valuation radius,
providing certified robustness. -/



/-! ## Section 13: Quantum Entropy Witness from Tropical Peak -/


/-! ## Section 14: Symmetric Ultrametric Measurement Echo -/


/-! ## Section 15: Additional Transfer Lemmas -/





end


