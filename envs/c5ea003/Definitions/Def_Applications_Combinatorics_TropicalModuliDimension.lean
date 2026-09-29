-- Prove2me | Definitions.Def_Applications_Combinatorics_TropicalModuliDimension
-- name    : Applications_Combinatorics_TropicalModuliDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:37.072348+00:00
-- url     : https://prove2.me/theorems/f1b8842b-6400-4fae-af02-639dc76b22bc
-- title:
--   Aether Catalog definitions — Applications_Combinatorics_TropicalModuliDimension
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Combinatorics.TropicalModuliDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Combinatorics/TropicalModuliDimension.lean by skeleton subtraction
import Mathlib

/-!
# Cone-complex dimension theory of the tropical moduli space `M_g^trop`

This file develops the **numerical / combinatorial backbone** of the tropical moduli
space of curves `M_g^trop`.  A point of `M_g^trop` is a *tropical curve*: a connected
metric weighted graph.  Its **combinatorial type** forgets the edge lengths and keeps
only the underlying connected stable weighted graph.  We record such a type by its
numerical invariants in the structure `StableType`:

* `vert0`   — number of weight-`0` vertices,
* `vertPos` — number of positive-weight vertices,
* `edges`   — number of edges,
* `weight`  — total vertex weight `W = Σ_v w(v)`,
* `genus`   — the genus `g`.

These satisfy three structural relations coming from the geometry of stable curves:

* **genus formula** (connectedness + definition of genus):
    `g + v = e + 1 + W`,  where `v = vert0 + vertPos`,
    equivalently `g = b₁ + W` with first Betti number `b₁ = e − v + 1`;
* **stability**:  every vertex `x` satisfies `2 w(x) − 2 + val(x) > 0`; summing over
    vertices and using the handshake lemma `Σ val = 2e` gives `3 v ≤ 2 W + 2 e`;
* **connectedness**:  `v ≤ e + 1`.

From these purely linear facts we obtain the classical dimension bounds of
Brannetti–Melo–Viviani / Caporaso:

* `StableType.vertex_bound` :  `v + 2 ≤ 2 g`     (i.e. `v ≤ 2g − 2`),
* `StableType.edge_bound`   :  `e + 3 ≤ 3 g`     (i.e. `e ≤ 3g − 3`),
* `StableType.jacobianDim_eq` / `jacobianDim_nonneg` :  the tropical Jacobian has
  dimension `b₁ = g − W ≥ 0`,
* `stableTypes_finite` :  for fixed `g` there are only finitely many types, so the
  cone complex is a *finite* fan,
* `trivalent_dimension` :  the top-dimensional cones (`e = 3g − 3`, `v = 2g − 2`,
  `W = 0`) are realised by honest connected **3-regular** `SimpleGraph`s, via the
  handshake lemma `SimpleGraph.sum_degrees_eq_twice_card_edges`.

The genus-`0` picture (`tree_genus_zero`, `genus_zero_no_edges_bound`) drops out as
the special case `b₁ = 0`.

-- !-- Lab Notebook -- !--
Hypothesis:  The dimension theory of `M_g^trop` (bounds `e ≤ 3g−3`, `v ≤ 2g−2`,
  finiteness of the fan, top cones = trivalent graphs) is, after the handshake lemma
  is applied, a purely *linear-arithmetic* consequence of the genus formula and
  stability inequality.  No analysis or scheme theory is required.
Result:  Confirmed.  All five headline theorems reduce to `omega` once the geometry
  is encoded as the three linear relations of `StableType`, and the trivalent
  realisation reduces to Mathlib's handshake lemma plus `omega`/`linarith`.
Insight:  Encoding the genus formula *additively* (`g + v = e + 1 + W`) instead of as
  `g = e − v + 1 + W` removes every truncated `ℕ`-subtraction, so `omega` sees the
  true integer geometry.  The single inequality `3v ≤ 2W + 2e` already packages
  stability + handshake and is exactly what powers both dimension bounds.
Failure analysis:  An earlier `vert`-only encoding (no split into `vert0`/`vertPos`)
  could not express the trivalence equality `3v = 2e`; splitting the vertex count and
  carrying `vertPos ≤ weight` was necessary to make the genus-`g` single-vertex type
  and the trivalent type both legal and to keep the bounds tight.
-/

namespace TropicalModuli

/-- The combinatorial type of a connected stable weighted graph (a point of
`M_g^trop` with its edge lengths forgotten), recorded by its numerical invariants.
`vert0` counts weight-`0` vertices, `vertPos` counts positive-weight vertices,
`edges` the edges, `weight` the total vertex weight, `genus` the genus. -/
structure StableType where
  vert0 : ℕ
  vertPos : ℕ
  edges : ℕ
  weight : ℕ
  genus : ℕ
  /-- Genus formula `g + v = e + 1 + W` (connectedness + `g = b₁ + W`). -/
  genus_formula : genus + (vert0 + vertPos) = edges + 1 + weight
  /-- Stability summed over vertices with the handshake lemma: `3v ≤ 2W + 2e`. -/
  stability : 3 * (vert0 + vertPos) ≤ 2 * weight + 2 * edges
  /-- Connectedness: a connected graph has `v ≤ e + 1`. -/
  connected : vert0 + vertPos ≤ edges + 1
  /-- Each positive-weight vertex carries weight `≥ 1`, so `vertPos ≤ W`. -/
  weight_pos : vertPos ≤ weight

namespace StableType

variable (S : StableType)

/-- Total number of vertices `v = vert0 + vertPos`. -/
def verts : ℕ := S.vert0 + S.vertPos

/-- The first Betti number `b₁ = e − v + 1`, i.e. the dimension of the tropical
Jacobian (the cycle space).  Taken in `ℤ` so the formula is honest. -/
def jacobianDim : ℤ := (S.edges : ℤ) - (S.verts : ℤ) + 1

-- !-- comment -- !--
-- `vertex_bound`: sum the stability terms (`3v ≤ 2W+2e`) against the genus formula
-- `g+v = e+1+W`; the weights and edges cancel, leaving `v ≤ 2g−2`.  Pure `omega`.
-- !-- comment -- !--

-- !-- comment -- !--
-- `edge_bound`: from the genus formula `e = g + v − 1 − W`, bound `v ≤ 2g−2` and
-- drop `W ≥ 0`.  Equivalent to `e ≤ 3g−3`.  Pure `omega`.
-- !-- comment -- !--

-- !-- comment -- !--
-- `jacobianDim_eq`: `b₁ = e − v + 1` and the genus formula give `b₁ = g − W`.
-- !-- comment -- !--

-- !-- comment -- !--
-- `jacobianDim_nonneg`: connectedness `v ≤ e+1` makes `e − v + 1 ≥ 0`.
-- !-- comment -- !--


-- !-- comment -- !--
-- `tree_genus_zero`: a weight-`0` tree (`e + 1 = v`) has `b₁ = 0`, hence genus `0`.
-- !-- comment -- !--

end StableType

/-! ## Finiteness of the fan -/

/-- A 4-tuple `(vert0, vertPos, edges, weight)` is a *legal invariant vector* of a
genus-`g` stable type when it satisfies the genus formula, stability, connectedness
and `vertPos ≤ weight`. -/
def IsGenusType (g : ℕ) : ℕ × ℕ × ℕ × ℕ → Prop
  | (v0, vp, e, w) =>
      g + (v0 + vp) = e + 1 + w ∧
      3 * (v0 + vp) ≤ 2 * w + 2 * e ∧
      v0 + vp ≤ e + 1 ∧
      vp ≤ w

-- !-- comment -- !--
-- `stableTypes_finite`: every legal vector is bounded — `v ≤ 2g`, `e ≤ 3g`, `w ≤ g` —
-- so the legal set injects into a finite box `range(2g+1) ×ˢ … ` and is finite.
-- !-- comment -- !--

/-! ## Trivalent realisation: top cones come from honest 3-regular graphs -/

-- !-- comment -- !--
-- `trivalent_dimension`: the handshake lemma `Σ deg = 2e` with `deg ≡ 3` gives
-- `3·|V| = 2·|E|`; combined with `b₁ = |E| − |V| + 1` this forces `|V| = 2b₁ − 2`
-- and `|E| = 3b₁ − 3`, the top-dimensional (codimension-`0`) cone of `M_g^trop`.
-- !-- comment -- !--

/-- The bundled genus-`g` *top type*: the trivalent combinatorial type with
`v = 2g − 2` weight-`0` vertices and `e = 3g − 3` edges (defined for `g ≥ 2`).  It
witnesses that the edge bound `e ≤ 3g − 3` is sharp. -/
def topType (g : ℕ) (hg : 2 ≤ g) : StableType where
  vert0 := 2 * g - 2
  vertPos := 0
  edges := 3 * g - 3
  weight := 0
  genus := g
  genus_formula := by omega
  stability := by omega
  connected := by omega
  weight_pos := by omega

-- !-- comment -- !--
-- `topType_edge_bound_sharp`: the bundled top type attains `e = 3g − 3`, so the
-- dimension bound `edge_bound` is sharp for every `g ≥ 2`.
-- !-- comment -- !--

end TropicalModuli


