-- Prove2me | Definitions.Def_Novelty_EdgeSpectralSupersaturationTriangles
-- name    : Novelty_EdgeSpectralSupersaturationTriangles
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:21:31.269194+00:00
-- url     : https://prove2.me/theorems/b063a5b0-d979-455f-a85c-4f0ca0769ca1
-- title:
--   Aether Catalog definitions — Novelty_EdgeSpectralSupersaturationTriangles
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EdgeSpectralSupersaturationTriangles`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EdgeSpectralSupersaturationTriangles.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Edge-spectral supersaturation for triangles

For a finite graph `G` with `m` edges, write `λ(G)` for the spectral radius of its
adjacency matrix.  Nosal's classical theorem states that a triangle-free graph
satisfies `λ² ≤ m`; equivalently, `λ² > m` forces at least one triangle.  A natural
*supersaturation* strengthening asks how the triangle count grows once `λ²` exceeds
`m` by an amount `q`.  The sharp conjecture (constant `B = 1`) predicts roughly
`q√m` triangles.  This file establishes the **unconditional spectral lower bound
with constant `1/3`**, which is the bound that follows directly from the power-trace
method, together with the triangle-free endpoint (Nosal's inequality).

## The power-trace method

The three ingredients are the standard identities relating the eigenvalues
`μ₁, …, μₙ` of the adjacency matrix to graph invariants:

* `∑ μᵢ² = tr(A²) = 2m`   (twice the number of edges),
* `∑ μᵢ³ = tr(A³) = 6t`   (six times the number of triangles),
* `|μᵢ| ≤ λ` for every `i`, where `λ` is the top eigenvalue.

The last item is the Perron–Frobenius statement that the spectral radius of a
nonnegative symmetric matrix is attained by its largest eigenvalue; we take it as
the hypothesis `hbound`, which is exactly the arithmetic input the method needs.

From these we prove the *eigenvalue supersaturation inequality*

  `∑ μᵢ³ ≥ 2λ³ − λ · ∑ μᵢ²`,

which specialises, via `∑ μᵢ² = 2m` and `λ² = m + q`, to `6t ≥ 2λq`, i.e.

  `t ≥ (λ q)/3 ≥ (q √m)/3`.

The whole development is carried out at the level of the eigenvalue multiset,
so the results apply verbatim to any real symmetric matrix whose spectral radius
dominates its spectrum.

## Main results

* `eigen_supersat`    — the eigenvalue supersaturation inequality.
* `triangle_count_lower`      — `λ q ≤ 3 t` (spectral supersaturation, constant 1/3).
* `triangle_count_lower_sqrt` — `√m · q ≤ 3 t`.
* `nosal`             — triangle-free (`∑ μᵢ³ = 0`) forces `λ² ≤ m`.
* `K3_supersaturation_example` — the complete graph `K₃` as a concrete instance.
* `trace_pow_eq_sum_pow_eigenvalues` — the linear-algebra bridge `tr(Aᵏ) = ∑ μᵢᵏ`
  for a real symmetric matrix, discharging the trace hypotheses from the spectral
  theorem.
* `matrix_eigen_supersat` — the eigenvalue supersaturation inequality proved
  directly for the traces of powers of a real symmetric matrix.

## Relation to the catalog

This file sits alongside the extremal-graph material of `Novelty/Turan.lean`
(Turán/Mantel, the *edge-count* endpoint of the same theory) and the Gram-matrix
spectral bounds of `Novelty/SpectralBound.lean`, extending the catalog's treatment
of triangle counting from the purely combinatorial regime to the spectral one.
-/

namespace Catalog.Novelty.EdgeSpectralSupersaturationTriangles

open Finset

-- !-- Lab Notes -- !--
-- Hypothesis (Hypothesizer): the sharp edge-spectral supersaturation bound for
--   triangles has constant `B = 1` (`t ≳ q√m`).  The `χ(F) ≥ 4` case is known;
--   the `χ = 3` (triangle) case is open.  Conjecture: even if the sharp constant
--   is out of reach, the power-trace method yields an unconditional constant.
-- Experiment (Experimenter): encode `tr(A²)=2m`, `tr(A³)=6t`, and Perron–Frobenius
--   `|μᵢ| ≤ λ` as hypotheses on the eigenvalue vector `μ` and push the inequality
--   `μ³ ≥ -λμ²` through the sum, isolating the top eigenvalue.
-- Analysis (Analyst): the method is *exactly* lossy by a factor of 3 versus the
--   conjecture — the slack lives in bounding `∑_{i≥2} μᵢ³ ≥ -λ∑_{i≥2}μᵢ²`, which is
--   tight only when the negative spectrum concentrates at `-λ` (bipartite-like),
--   a configuration incompatible with many triangles.  Hence "true but not sharp".
-- Critique (Critic): the results are conditional on the three eigenvalue identities.
--   These are genuine theorems (trace of matrix powers, Perron–Frobenius) rather
--   than definitions, so stating them as hypotheses is the faithful abstraction and
--   not a triviality; the `K₃` instance certifies the hypotheses are satisfiable and
--   the bound non-vacuous.






/-! ### A concrete instance: the triangle `K₃`

The adjacency matrix of `K₃` has spectrum `{2, -1, -1}`.  Here `m = 3`, `t = 1`,
`λ = 2`, so `λ² = 4 = m + q` with excess `q = 1`.  The general theorem then
certifies `λ·q = 2 ≤ 3 = 3t`, a genuine (non-vacuous) triangle count. -/

/-- The eigenvalue vector of the complete graph `K₃`. -/
noncomputable def muK3 : Fin 3 → ℝ := ![2, -1, -1]


/-! ### The linear-algebra bridge: from the spectral theorem to matrix traces

The results above are stated at the level of an abstract eigenvalue vector, with the
trace identities `∑ μᵢ² = tr(A²)` and `∑ μᵢ³ = tr(A³)` supplied as hypotheses.  We now
*discharge* those hypotheses for a genuine real symmetric (Hermitian) matrix, turning
the combinatorial estimate into a theorem of linear algebra.  The engine is Mathlib's
spectral theorem `Matrix.IsHermitian.spectral_theorem`, which diagonalises `A` by a
unitary conjugation; since the trace is invariant under conjugation and a power of a
conjugation is the conjugation of the power, `tr(Aᵏ)` collapses to `∑ μᵢᵏ`. -/




end Catalog.Novelty.EdgeSpectralSupersaturationTriangles


