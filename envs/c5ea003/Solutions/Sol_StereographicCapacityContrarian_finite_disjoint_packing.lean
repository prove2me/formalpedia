-- Prove2me | solution 1 for StereographicCapacityContrarian.finite_disjoint_packing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:08:33.623147+00:00
-- url     : https://prove2.me/submissions/bc85fe87-5f82-4d5a-a622-053f2ee9f666

-- Sol generated from Geometry/StereographicCapacity/Contrarian.lean
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














open StereographicCapacityContrarian in
theorem solution    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (caps : ι → Set α) (ambient : Set α)
    (hmeas : ∀ i ∈ s, MeasurableSet (caps i))
    (hsub : ∀ i ∈ s, caps i ⊆ ambient)
    (hdisj : Set.PairwiseDisjoint (s : Set ι) caps)
    (v : ENNReal) (hvol : ∀ i ∈ s, v ≤ μ (caps i)) :
    s.card * v ≤ μ ambient := by
  calc (↑s.card : ENNReal) * v
      = ∑ _i ∈ s, v := by simp [Finset.sum_const]
    _ ≤ ∑ i ∈ s, μ (caps i) := by
        apply Finset.sum_le_sum fun i hi => hvol i hi
    _ = μ (⋃ i ∈ s, caps i) := by
        rw [MeasureTheory.measure_biUnion_finset hdisj hmeas]
    _ ≤ μ ambient := by
        apply MeasureTheory.measure_mono
        intro x hx
        obtain ⟨i, hi, hx_i⟩ := Set.mem_iUnion₂.mp hx
        exact hsub i hi hx_i
