-- Prove2me | Theorems.Thm_StereographicCapacityContrarian_finite_disjoint_packing
-- name    : StereographicCapacityContrarian.finite_disjoint_packing
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:11.170824+00:00
-- url     : https://prove2.me/theorems/78e5ff3f-2d84-4a12-8244-2e4f678f3f14
-- title:
--   Finite additivity gives the fundamental packing inequality.
-- statement:
--   Finite additivity gives the fundamental packing inequality.
--
--   ```lean
--   theorem StereographicCapacityContrarian.finite_disjoint_packing    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
--       (s : Finset ι) (caps : ι → Set α) (ambient : Set α)
--       (hmeas : ∀ i ∈ s, MeasurableSet (caps i))
--       (hsub : ∀ i ∈ s, caps i ⊆ ambient)
--       (hdisj : Set.PairwiseDisjoint (s : Set ι) caps)
--       (v : ENNReal) (hvol : ∀ i ∈ s, v ≤ μ (caps i)) :
--       s.card * v ≤ μ ambient := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/StereographicCapacity/Contrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/StereographicCapacity/Contrarian.lean#L33

-- Thm stub generated from Geometry/StereographicCapacity/Contrarian.lean
import Mathlib
import Definitions.Def_Geometry_StereographicCapacity_Contrarian

/-!
# Contrarian results for stereographic capacity on `S²`

This self-contained file separates the area argument from the proposed stereographic
correction and tests the claimed calibrations.  Caps of geodesic radius `r` have
area `2π(1-cos r)`.  Pairwise disjoint caps therefore satisfy the stronger direct
area bound `card ≤ 2/(1-cos r)`.

The proposed correction `(2/cos r)^2` does not tend to one: at `r = 0` it equals
four.  Moreover, four caps of radius `π/3` cannot be packed.  Their centers would
be unit vectors with every mutual inner product at most `cos(2π/3) = -1/2`, which
contradicts nonnegativity of the squared norm of their sum.  Thus the advertised
"tetrahedral" calibration is false for caps of that radius.
-/

open scoped ENNReal
open MeasureTheory Set Finset Real

open StereographicCapacityContrarian

noncomputable section

theorem StereographicCapacityContrarian.finite_disjoint_packing    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (caps : ι → Set α) (ambient : Set α)
    (hmeas : ∀ i ∈ s, MeasurableSet (caps i))
    (hsub : ∀ i ∈ s, caps i ⊆ ambient)
    (hdisj : Set.PairwiseDisjoint (s : Set ι) caps)
    (v : ENNReal) (hvol : ∀ i ∈ s, v ≤ μ (caps i)) :
    s.card * v ≤ μ ambient := by sorry
