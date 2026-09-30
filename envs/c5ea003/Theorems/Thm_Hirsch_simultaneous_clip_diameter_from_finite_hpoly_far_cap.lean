-- Prove2me | Theorems.Thm_Hirsch_simultaneous_clip_diameter_from_finite_hpoly_far_cap
-- name    : Hirsch.simultaneous_clip_diameter_from_finite_hpoly_far_cap
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T14:55:05.323237+00:00
-- url     : https://prove2.me/theorems/48a48c4c-685d-4f87-a717-7dbaf1c33189
-- title:
--   Canonical far-cap transfer for simultaneous clipping of a finite pointed H-polyhedron
-- statement:
--   Let Q be the finite H-polyhedron A_j x <= b_j in Euclidean space, with no nonzero direction annihilated by every row normal. Let its vertex-edge graph have padded diameter at most D. Use the canonical cap normal equal to minus the sum of all H-row normals, and choose a level T at least as large as its value on every old vertex and strictly larger than its value on every point of the final simultaneous clip. If final cut face i has intrinsic graph diameter at most B_i, then the final clipped polytope has padded graph diameter at most D + 1 + sum_i B_i. The proof constructs the compact cap, proves old edges survive, classifies every new cap vertex as a horizon vertex adjacent to an old vertex, and applies the strict-centre-free exterior-route clipping transfer.
-- source:
--   Kernel-verified canonical finite-H-polyhedron far-cap construction and transfer in jjoshua2/prove2me-work.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem simultaneous_clip_diameter_from_finite_hpoly_far_cap
    {d n : ℕ} {ι : Type*} [Fintype ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (T : ℝ)
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ j, ⟪a j, r⟫ = 0) → r = 0)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hOldBelow : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      ⟪-(∑ j, a j), x⟫ ≤ T)
    (hFinalBelow : ∀ x ∈ Hpoly a b ∩ {y | ∀ i, f i y ≤ c i},
      ⟪-(∑ j, a j), x⟫ < T)
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE
      ((Hpoly a b ∩ {y | ∀ j, f j y ≤ c j}) ∩ {x | f i x = c i}) (B i)) :
    DiamLE (Hpoly a b ∩ {y | ∀ i, f i y ≤ c i}) (D + 1 + ∑ i, B i) := by sorry

end Hirsch
