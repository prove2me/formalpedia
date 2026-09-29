-- Prove2me | Definitions.Def_Speculative_NumberTheory_ChipFiring
-- name    : Speculative_NumberTheory_ChipFiring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:43:02.149261+00:00
-- url     : https://prove2.me/theorems/25b31e2b-b765-4adf-8361-3a923dcc9423
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_ChipFiring
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.ChipFiring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/ChipFiring.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.ChipFiring

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 19
-/

noncomputable section

/-- A graph divisor is an integer-valued function on vertices. -/
abbrev GraphDivisor (n : ℕ) := Fin n → ℤ

/-- The degree of a divisor. -/
def divisorDeg {n : ℕ} (D : GraphDivisor n) : ℤ := ∑ i : Fin n, D i

/-- A graph Laplacian for divisor theory. -/
structure GraphLapl (n : ℕ) where
  L : Matrix (Fin n) (Fin n) ℤ
  symmetric : L.IsSymm
  row_sum_zero : ∀ i : Fin n, ∑ j : Fin n, L i j = 0

/-- A principal divisor. -/
def IsPrincipal {n : ℕ} (grL : GraphLapl n) (D : GraphDivisor n) : Prop :=
  ∃ f : Fin n → ℤ, ∀ i, D i = ∑ j : Fin n, grL.L i j * f j

/-- Linear equivalence: D₁ ~ D₂ iff D₁ - D₂ is principal. -/
def GraphLinEquiv {n : ℕ} (grL : GraphLapl n) (D₁ D₂ : GraphDivisor n) : Prop :=
  IsPrincipal grL (D₁ - D₂)







/-- Chip-firing at vertex v. -/
def chipFire {n : ℕ} (grL : GraphLapl n) (D : GraphDivisor n) (v : Fin n) : GraphDivisor n :=
  fun i => D i - grL.L v i


/-- The graph genus: g = |E| - |V| + 1. -/
def graphGenus (numEdges numVertices : ℕ) : ℤ :=
  (numEdges : ℤ) - (numVertices : ℤ) + 1

/-- The degree of vertex i: deg(i) = -L(i,i). -/
def vertexDegree {n : ℕ} (grL : GraphLapl n) (i : Fin n) : ℤ := -grL.L i i

/-- The canonical divisor K(v) = deg(v) - 2. -/
def canonicalDivisor {n : ℕ} (grL : GraphLapl n) : GraphDivisor n :=
  fun i => vertexDegree grL i - 2




end


