-- Prove2me | Definitions.Def_Bridges_ChipFiring_ChipFiring
-- name    : Bridges_ChipFiring_ChipFiring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T10:10:54.645821+00:00
-- url     : https://prove2.me/theorems/e6783d59-f4bb-4d7f-bb45-264a3866b82f
-- title:
--   Aether Catalog definitions — Bridges_ChipFiring_ChipFiring
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ChipFiring.ChipFiring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ChipFiring/ChipFiring.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.ChipFiring

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 19
-/

noncomputable section

/-- A graph divisor is an integer-valued function on vertices. -/
abbrev GraphDivisor (numEdges : ℕ) := Fin numEdges → ℤ

/-- The degree of a divisor. -/
def divisorDeg {numEdges : ℕ} (D : GraphDivisor numEdges) : ℤ := ∑ i : Fin numEdges, D i

/-- A graph Laplacian for divisor theory. -/
structure GraphLapl (numEdges : ℕ) where
  L : Matrix (Fin numEdges) (Fin numEdges) ℤ
  symmetric : L.IsSymm
  row_sum_zero : ∀ i : Fin numEdges, ∑ j : Fin numEdges, L i j = 0

/-- A principal divisor. -/
def IsPrincipal {numEdges : ℕ} (grL : GraphLapl numEdges) (D : GraphDivisor numEdges) : Prop :=
  ∃ f : Fin numEdges → ℤ, ∀ i, D i = ∑ j : Fin numEdges, grL.L i j * f j

/-- Linear equivalence: D₁ ~ D₂ iff D₁ - D₂ is principal. -/
def GraphLinEquiv {numEdges : ℕ} (grL : GraphLapl numEdges) (D₁ D₂ : GraphDivisor numEdges) : Prop :=
  IsPrincipal grL (D₁ - D₂)







/-- Chip-firing at vertex v. -/
def chipFire {numEdges : ℕ} (grL : GraphLapl numEdges) (D : GraphDivisor numEdges) (v : Fin numEdges) : GraphDivisor numEdges :=
  fun i => D i - grL.L v i


/-- The graph genus: g = |E| - |V| + 1. -/
def graphGenus (numEdges numVertices : ℕ) : ℤ :=
  (numEdges : ℤ) - (numVertices : ℤ) + 1

/-- The degree of vertex i: deg(i) = -L(i,i). -/
def vertexDegree {numEdges : ℕ} (grL : GraphLapl numEdges) (i : Fin numEdges) : ℤ := -grL.L i i

/-- The canonical divisor K(v) = deg(v) - 2. -/
def canonicalDivisor {numEdges : ℕ} (grL : GraphLapl numEdges) : GraphDivisor numEdges :=
  fun i => vertexDegree grL i - 2




end


