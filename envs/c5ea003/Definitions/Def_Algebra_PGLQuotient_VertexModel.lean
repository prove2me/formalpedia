-- Prove2me | Definitions.Def_Algebra_PGLQuotient_VertexModel
-- name    : Algebra_PGLQuotient_VertexModel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:26:19.354545+00:00
-- url     : https://prove2.me/theorems/9494b358-7f2b-44c4-b1fb-13a40c680c63
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_VertexModel
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.VertexModel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/VertexModel.lean by skeleton subtraction
import Mathlib

/-!
# The standard arithmetic quotient of `PGL_d`: the vertex model

This file sets up an explicit combinatorial model for the vertex set of the standard
non-uniform arithmetic quotient of the affine Bruhat–Tits building of
`PGL_d (F_q((t^{-1})))` by `Γ = PGL_d(F_q[t])`.

By Soulé's theorem the quotient `Γ \ X` is (simplicially) a dominant sector: its vertices are
in bijection with dominant coweights `λ = (λ_0 ≥ λ_1 ≥ ⋯ ≥ λ_{d-1} = 0)`, and the stabiliser
of the vertex `λ` in `GL_d(F_q[t])` is the group of matrices `(a_{ij})` over `F_q[t]` with
`deg a_{ij} ≤ λ_i - λ_j`; equivalently, it is the automorphism group of the vector bundle
`⨁_i O(λ_i)` on `P^1`, i.e. the unit group of the algebra `End = ⨁_{i,j} H^0(O(λ_i - λ_j))`.
Its order is

`|Aut(λ)| = q^{dim End} * ∏_i (1 - q^{-r_i})`,

where `dim End = ∑_{i,j} max (0, λ_i - λ_j + 1)` and `r_i = #{ j ≤ i : λ_j = λ_i }` is the
position of `i` inside its block of equal entries (so that the second factor accounts for the
Levi `∏_b GL_{m_b}(F_q)` of the block composition).  With the Haar measure normalised so that
a maximal compact subgroup has volume `1`, the vertex `λ` carries the mass `1/|Aut(λ)|`
(`GL`-normalisation) resp. `(q-1)/|Aut(λ)|` (`PGL`-normalisation).

Vertices are parametrised here by their *gaps* `g_k = λ_k - λ_{k+1} ∈ ℕ`, `0 ≤ k ≤ d-2`, i.e.
by `Vertex d = Fin (d-1) → ℕ`.

The homothety-invariant normalised lattice-minima height is
`α(λ) = q^{λ_0 - (λ_0 + ⋯ + λ_{d-1})/d}`, which in gap coordinates reads
`log_q α = (∑_k (d-1-k) g_k)/d`.

## Main results of this file

* `sum_lam_sub_eq_pairExp` : the cut-set/double-counting identity
  `∑_{i,j} (λ_i - λ_j) = ∑_k (k+1)(d-1-k) g_k`;
* `vertexWeight_le`, `vertexWeight_ge` : sharp-order two-sided bounds
  `c₁ q^{-P(g)} ≤ 1/|Aut(λ)| ≤ c₂ q^{-P(g)}` with `P(g) = ∑_k (k+1)(d-1-k) g_k`.

These drive all the analytic results (integrability threshold, cusp tail, height zeta
function) in the companion files.
-/

namespace PGLQuotient

open Finset

/-- Vertices of the standard quotient in gap coordinates: `g k = λ_k - λ_{k+1}`. -/
abbrev Vertex (d : ℕ) : Type := Fin (d - 1) → ℕ

variable {d : ℕ}

/-- The `k`-th gap, extended by `0` outside the range. -/
def gapAt (g : Vertex d) (k : ℕ) : ℕ := if h : k < d - 1 then g ⟨k, h⟩ else 0

/-- The dominant coweight attached to a gap vector: `λ_i = ∑_{k ≥ i} g_k`. -/
def lam (g : Vertex d) (i : ℕ) : ℕ := ∑ k ∈ Finset.Ico i (d - 1), gapAt g k

/-- `dim_{F_q} End(⨁_i O(λ_i)) = ∑_{i,j} max (0, λ_i - λ_j + 1)`. -/
def endDim (g : Vertex d) : ℕ := ∑ i ∈ range d, ∑ j ∈ range d, (lam g i + 1 - lam g j)

/-- The position of `i` inside its block of equal coweight entries. -/
def blockRank (g : Vertex d) (i : ℕ) : ℕ :=
  ((range (i + 1)).filter (fun j => lam g j = lam g i)).card

/-- The order of the stabiliser `Aut(⨁_i O(λ_i))` of the vertex `g` in `GL_d(F_q[t])`. -/
noncomputable def autOrder (q : ℝ) (g : Vertex d) : ℝ :=
  q ^ endDim g * ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i)

/-- The mass carried by a vertex of the quotient (Haar normalised by `vol(K) = 1`). -/
noncomputable def vertexWeight (q : ℝ) (g : Vertex d) : ℝ := (autOrder q g)⁻¹

/-- `d * log_q α`, the numerator of the normalised lattice-minima height. -/
def heightExp (g : Vertex d) : ℕ := ∑ k ∈ range (d - 1), (d - 1 - k) * gapAt g k

/-- The residual exponent `∑_k k (d-1-k) g_k`. -/
def resExp (g : Vertex d) : ℕ := ∑ k ∈ range (d - 1), k * (d - 1 - k) * gapAt g k

/-- The pair exponent `∑_{i<j} (λ_i - λ_j) = ∑_k (k+1)(d-1-k) g_k`. -/
def pairExp (g : Vertex d) : ℕ := ∑ k ∈ range (d - 1), (k + 1) * (d - 1 - k) * gapAt g k

/-- The homothety-invariant normalised lattice-minima height `α`. -/
noncomputable def height (q : ℝ) (g : Vertex d) : ℝ := q ^ ((heightExp g : ℝ) / d)

section Combinatorics

variable (g : Vertex d)









end Combinatorics

section Bounds

variable {q : ℝ} (g : Vertex d)












end Bounds

end PGLQuotient


