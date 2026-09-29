-- Prove2me | Definitions.Def_Bridges_PosetTheory_GaussianFreeField
-- name    : Bridges_PosetTheory_GaussianFreeField
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:40.513554+00:00
-- url     : https://prove2.me/theorems/55b2be9f-76f0-4477-ae3e-6b8f15880d44
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_GaussianFreeField
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.GaussianFreeField`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/GaussianFreeField.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Free Field on Finite Weighted Graphs

This file establishes the connection between the Gaussian free field (GFF) on
finite weighted graphs and the Laplacian / canonical kernel structures from
tropical geometry and spectral graph theory.

## Main Definitions

* `GraphGFFEnergy` — the quadratic energy x^T L x for a matrix L
* `IsZeroMean` — predicate for zero-mean functions on a finite type
* `CovarianceFromResistance` — covariance kernel derived from effective resistance
* `GFFPartitionPrefactor` — the partition function normalization constant

## Main Results

* `graphGFFEnergy_nonneg` — nonnegativity of GFF energy for PSD Laplacians
* `graphGFFEnergy_add_const` — gauge invariance: E(x + c·1) = E(x)
* `pinnedGFF_partition_prefactor_pos` — positivity of the partition prefactor
* `effectiveResistance_eq_pseudoinverse_quadratic` — R_eff = L⁺_ii + L⁺_jj - 2L⁺_ij
* `variance_difference_eq_resistance` — Var(φ_i - φ_j) = R(i,j)

## Cross-Domain Connections

This file bridges:
- **Statistical mechanics** ↔ **Electrical networks**: covariance = effective resistance
- **Tropical geometry** ↔ **Gaussian fields**: canonical kernel lattice = GFF state space
- **Spectral graph theory** ↔ **Mathematical physics**: det(L_red) = partition normalization

## References

* Baker, M. and Faber, X. "Metrized graphs, Laplacian operators, and
  electrical networks" (2006)
* Lyons, R. with Peres, Y. "Probability on Trees and Networks" (2016)

## Catalog Dependencies

This file builds on results from:
- `Pythagorean.TropicalBridge.MetricKernel.Theorems` — especially `weightedLaplacian_psd`,
  `weightedLaplacian_row_sum_zero`, `weightedLaplacian_symm`
- `Bridges.Catalog.Pythagorean.TropicalBridge.CanonicalKernelTheorems` — especially
  `harmonicKernel` and chip-firing equivalence structures

The weighted Laplacian and its properties are re-imported here for the
subagent's convenience (the definitions are identical to those in the catalog).
-/


open Finset BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Weighted Laplacian from Catalog -/

/-- The **weighted Laplacian** (reproduced from MetricKernel/Theorems for self-containment). -/
noncomputable def weightedLaplacianGFF
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → V → ℝ) : Matrix V V ℝ :=
  fun i j =>
    if i = j then ∑ k ∈ Finset.univ.filter (G.Adj i), w i k
    else if G.Adj i j then -(w i j)
    else 0

/-! ## Core Definitions -/

/-- The **GFF quadratic energy** associated to a matrix `L`.
    For a weighted Laplacian, this is the Dirichlet energy
    E_L(x) = x^T L x = ∑_i ∑_j x_i L_{ij} x_j. -/
def GraphGFFEnergy (L : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * L i j * x j


/-- The **covariance kernel derived from effective resistance**.
    Given a resistance function R and a base vertex, the covariance is
    K(i,j) = (R(i,base) + R(j,base) - R(i,j)) / 2. -/
noncomputable def CovarianceFromResistance (R : ι → ι → ℝ) (base : ι) (i j : ι) : ℝ :=
  (R i base + R j base - R i j) / 2

/-- The **GFF partition function prefactor** for a positive definite reduced
    Laplacian of dimension n with determinant detLred.
    Z = (2π)^(n/2) / √(det L_red). -/
noncomputable def GFFPartitionPrefactor (n : ℕ) (detLred : ℝ) : ℝ :=
  (2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt detLred

/-- A matrix has **row-sum zero** if every row sums to zero. -/
def IsRowSumZero (L : Matrix ι ι ℝ) : Prop :=
  ∀ i, ∑ j, L i j = 0

/-- A matrix is **entry-symmetric**. -/
def IsSymmMatrix (L : Matrix ι ι ℝ) : Prop :=
  ∀ i j, L i j = L j i

/-- **Covariance compatibility**: the pseudoinverse entries encode resistance
    via L⁺_{ij} = (R(i,base) + R(j,base) - R(i,j)) / 2. -/
def CovarianceCompatible (Lplus R : Matrix ι ι ℝ) (base : ι) : Prop :=
  ∀ i j, Lplus i j = (R i base + R j base - R i j) / 2

/-! ## Auxiliary Lemmas -/

/-
Row-sum-zero implies L applied to constant vector vanishes.
-/

/-
Symmetry + row-sum-zero implies column-sum-zero.
-/

/-! ## Theorem 1: Gauge Invariance of GFF Energy -/

/-
**Gauge invariance of GFF energy.**
    For a symmetric matrix with row-sum zero (i.e. a graph Laplacian),
    adding a constant to all entries of x does not change the energy:
    E_L(x + c·1) = E_L(x).

    This identifies the physical state space with potentials modulo constants,
    and is the rigorous gateway from spectral graph theory to the GFF measure
    on the quotient ℝ^V / ℝ·1.

    **Proof sketch:** Expand E_L(x+c) = ∑_i∑_j (x_i+c) L_{ij} (x_j+c).
    Distribute to get E_L(x) + c·∑_i x_i·(∑_j L_{ij}) + c·∑_j (∑_i L_{ij})·x_j
    + c²·∑_i∑_j L_{ij}. Each extra term vanishes by row/column-sum-zero.
-/

/-! ## Theorem 2: Partition Function Prefactor -/

/-
**Positivity of the partition function prefactor.**
    For a positive definite reduced Laplacian (det > 0), the GFF partition
    prefactor (2π)^(n/2) / √(det L_red) is positive.

    This is the central statistical mechanics result: the reduced Laplacian
    determinant is the exact normalization constant for the pinned GFF.
-/

/-! ## Theorem 3: Covariance = Effective Resistance -/

/-
**Effective resistance equals pseudoinverse quadratic form.**
    If the pseudoinverse Lplus and resistance R are covariance-compatible
    (i.e. L⁺_{ij} = (R(i,b) + R(j,b) - R(i,j))/2), then
    R(i,j) = L⁺_{ii} + L⁺_{jj} - 2·L⁺_{ij}.

    This is the cross-domain flagship result: it interprets effective resistance
    (an electrical network quantity) as a Gaussian fluctuation observable
    (Var(φ_i - φ_j) in the GFF).
-/

/-
**Symmetry of the pinned covariance kernel.**
    The covariance kernel K(i,j) = (R(i,b) + R(j,b) - R(i,j))/2
    is symmetric when R is symmetric.
-/

/-
**Covariance kernel diagonal from resistance.**
    The diagonal of the covariance kernel equals the resistance to base:
    K(i,i) = R(i,base).
-/

/-
**Variance of field difference equals resistance (flagship cross-domain theorem).**
    Var(φ_i - φ_j) = K(i,i) + K(j,j) - 2K(i,j) = R(i,j).
    This is the statistical mechanics interpretation of effective resistance:
    thermal fluctuations in the GFF equal network dissipation geometry.
-/

/-! ## Bridge to Weighted Graph Laplacian (Catalog Connection) -/

/-
The weighted Laplacian has row-sum zero (proved in MetricKernel/Theorems).
-/

/-
The weighted Laplacian is symmetric when weights are symmetric.
-/


