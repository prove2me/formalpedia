-- Prove2me | Theorems.Thm_BookSixth_orthonormal_frame_cross_unit_euclidean
-- name    : BookSixth.orthonormal_frame_cross_unit_euclidean
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-28T02:17:24.746525+00:00
-- url     : https://prove2.me/theorems/02898b78-1218-48f8-9fb7-2bc1b8202914
-- title:
--   The cross product of an orthonormal pair is a Euclidean unit vector perpendicular to the plane they span
-- statement:
--   Let `u`, `v` be an orthonormal pair in `Space3 = Fin 3 → ℝ`, in the sense used by `RoundCircle`:
--
--     * `(∑ i, u i * u i) = 1`
--     * `(∑ i, v i * v i) = 1`
--     * `(∑ i, u i * v i) = 0`
--
--   Then `w := u ⨯₃ v` is a **unit vector in the Euclidean norm** and is perpendicular to both `u` and `v`.
--
--   Two remarks that matter for the geometry.
--
--   First, the norm here is genuinely the Euclidean one. `Space3` carries the supremum norm, in which every vector of the frame satisfies `‖u‖ = 1` as soon as one coordinate is `±1`; the conditions in `RoundCircle` are instead the *square* of the Euclidean norm, `∑ u i * u i = ‖u‖₂ ^ 2`. So `u ⨯₃ v` is a unit vector for `‖·‖₂` and not for `‖·‖_∞`.
--
--   Second, orthonormality of the pair forces `‖u ⨯₃ v‖₂ = 1` rather than merely `≤ 1`. This is Lagrange's identity `‖u × v‖² = ‖u‖²‖v‖² − (u·v)² = 1`.
--
--   This is the unit normal required to write the plane of a round circle as `{x : (x - c) • w = 0}` in the hemisphere construction of the Freedman–Skora shrinking argument.
-- source:
--   **The identity.** `Mathlib.LinearAlgebra.CrossProduct.cross_dot_cross` is the scalar quadruple product identity
--
--   ```
--   u ⨯₃ v ⬝ᵥ w ⨯₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w
--   ```
--
--   Substituting `w := u` and `x := v` gives
--
--   ```
--   ‖u × v‖₂ ^ 2 = (u · u) * (v · v) - (u · v) ^ 2 = 1 * 1 - 0 = 1,
--   ```
--
--   which is Lagrange's identity specialised to an orthonormal pair.
--
--   **Perpendicularity.** `dot_self_cross` and `dot_cross_self` in the same file give `u ⬝ᵥ u ⨯₃ v = 0` and `v ⬝ᵥ u ⨯₃ v = 0` outright.
--
--   **Bridging the two dot products.** `u ⬝ᵥ w` is `Matrix.dotProduct`, whose coordinate form is `∑ i, u i * w i`; this is exactly the sum appearing in the statement, so `Pi.inner` and the coordinate sum agree definitionally at `Fin 3`.

import Mathlib
import Definitions.Def_BookSixth
import Mathlib.LinearAlgebra.CrossProduct
open scoped BigOperators
open BookSixth
open Matrix

theorem BookSixth.orthonormal_frame_cross_unit_euclidean (u v w : Space3) (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) : w = u ⨯₃ v ∧ (∑ i, w i * w i) = 1 ∧ (∑ i, w i * u i) = 0 ∧ (∑ i, w i * v i) = 0 := by sorry
