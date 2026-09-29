-- Prove2me | Definitions.Def_Novelty_NaturalExtensionInvolution
-- name    : Novelty_NaturalExtensionInvolution
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:58.962367+00:00
-- url     : https://prove2.me/theorems/b6397ff6-0a36-438c-8511-78efc3ebd4c6
-- title:
--   Aether Catalog definitions — Novelty_NaturalExtensionInvolution
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NaturalExtensionInvolution`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NaturalExtensionInvolution.lean by skeleton subtraction
import Mathlib
/-
# A Measure-Preserving Involution on the Natural-Extension Model of the Triangle Map

We work with a faithful *planar model* of the natural-extension domain of the triangle map
(a multidimensional continued-fraction algorithm): the unit square, split into four congruent
subdomains `D₁, D₂, D₃, D₄` by its two mid-lines.  The **conjugation involution** `τ`, given by
the central point reflection `τ(x, y) = (1, 1) - (x, y)`, is the geometric shadow of Young
conjugation of partitions (see `YoungConjugation.lean`): it exchanges the roles of the two
coordinates' complements exactly as conjugation exchanges rows and columns of a diagram.

We prove that `τ` is:
* an involution (`tau_involutive`),
* measure preserving for Lebesgue measure (`tau_measurePreserving`),
* a permutation of the four subdomains as two transpositions `D₁ ↔ D₃`, `D₂ ↔ D₄`
  (`tau_image_D1 … tau_image_D4`),

and that the four subdomains are pairwise disjoint, each of Lebesgue measure exactly `1/4`, and
together exhaust the whole domain (`measure_Di`, `subdomains_disjoint*`, `measure_domain_eq_one`).

-- !-- Lab Notes -- !--
Hypothesis (H2): The natural extension carries a `ℤ/2ℤ` symmetry `τ` that (a) preserves the
  invariant measure and (b) splits the domain into four equal-mass cells that `τ` permutes.
Experiment: We modelled the domain as `[0,1]²` with the mid-line partition and took `τ` to be the
  point reflection through the centre `(1/2, 1/2)`.  Computation of `τ '' D₁` returned `D₃`
  exactly (matching half-open conventions chosen so `τ` is a genuine set bijection), and each
  `volume Dᵢ` came out to `1/4` via `Measure.prod_prod` on `Ico/Set.Ioc` intervals.
Analysis: The equal-mass property is *forced*, not assumed: measure preservation of `τ` already
  equates `volume D₁ = volume D₃` and `volume D₂ = volume D₄`, while the direct interval
  computation pins every cell to `1/4`.  The two facts are mutually consistent — a good sanity
  check that the model is not degenerate.
Failure analysis: A first attempt used `Ico` for all four cells; then `τ '' D₁` was `Set.Ioc … ×ˢ Set.Ioc …`,
  which is *not* literally `D₃`.  Fixing the half-open orientation of each cell so that reflection
  maps closed ends to open ends made the set images exact — a reminder that "up to measure zero"
  and "on the nose" are different statements and we chose to prove the stronger one.
Critique: `measure_union` needs measurability + disjointness of the accumulated union with the
  next cell; we discharge these with `Disjoint.union_left`, so `measure_domain_eq_one` is a real
  additivity computation, not `simp`.
Synthesis: `τ` is a bona-fide measure-preserving involution with a four-cell equal-mass orbit
  structure — the geometric incarnation of the algebraic `ℤ/2ℤ` from `YoungConjugation.lean`.
-/

open MeasureTheory

namespace TriangleMap

noncomputable section

/-- South-West quarter of the model domain. -/
def D1 : Set (ℝ × ℝ) := Set.Ico 0 (1 / 2) ×ˢ Set.Ico 0 (1 / 2)
/-- South-East quarter. -/
def D2 : Set (ℝ × ℝ) := Set.Ioc (1 / 2) 1 ×ˢ Set.Ico 0 (1 / 2)
/-- North-East quarter. -/
def D3 : Set (ℝ × ℝ) := Set.Ioc (1 / 2) 1 ×ˢ Set.Ioc (1 / 2) 1
/-- North-West quarter. -/
def D4 : Set (ℝ × ℝ) := Set.Ico 0 (1 / 2) ×ˢ Set.Ioc (1 / 2) 1

/-- The **conjugation involution** on the natural-extension model: the central point reflection
`τ(x, y) = (1, 1) - (x, y)`. -/
def tau : ℝ × ℝ → ℝ × ℝ := fun p => ((1 : ℝ), (1 : ℝ)) - p



/-! ### Measurability of the four cells -/


/-! ### Each cell has measure `1/4` -/





/-! ### Pairwise disjointness -/


/-! ### `τ` permutes the four cells as two transpositions -/





/-! ### The four cells exhaust the domain -/

/-- The natural-extension model domain: the union of the four subdomains. -/
def domain : Set (ℝ × ℝ) := D1 ∪ D2 ∪ D3 ∪ D4



end

end TriangleMap


