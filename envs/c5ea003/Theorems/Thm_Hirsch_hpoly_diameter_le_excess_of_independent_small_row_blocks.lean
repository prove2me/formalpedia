-- Prove2me | Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_independent_small_row_blocks
-- name    : Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T20:26:51.273969+00:00
-- url     : https://prove2.me/theorems/27737675-3725-4a3d-92d7-92a87e91031e
-- title:
--   High-excess H-polyhedra factorized into small-excess row blocks satisfy the row-excess bound
-- statement:
--   Let P be a nonempty bounded H-polyhedron in R^d described by n rows. Suppose an invertible linear change of coordinates identifies its rows with a disjoint family of independent blocks: block i uses counts(i) rows in dims(i) coordinates, every parent row is in exactly one block, and each block has dims(i) <= counts(i) <= dims(i)+3. Then the padded ordinary vertex-edge graph diameter of P is at most n-d. There is no bound on total row excess n-d or on the number of factors. The conclusion follows from an actual Cartesian-product decomposition, not from a face-cover or an amortized circuit-count argument.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/4924c6ea81cda80c6a8bd54ce2a0d3d784525b3b ; standalone Lean/Axiom gate Actions run 34644132950

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem hpoly_diameter_le_excess_of_independent_small_row_blocks
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3) :
    DiamLE (Hpoly a b) (n - d) := by sorry
end Hirsch
