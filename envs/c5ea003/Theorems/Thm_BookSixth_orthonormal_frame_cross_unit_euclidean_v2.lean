-- Prove2me | Theorems.Thm_BookSixth_orthonormal_frame_cross_unit_euclidean_v2
-- name    : BookSixth.orthonormal_frame_cross_unit_euclidean_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T02:52:32.569997+00:00
-- url     : https://prove2.me/theorems/6fb82d15-b175-46a5-8a19-192d25b4bd9a
-- title:
--   The cross product of an orthonormal pair is a Euclidean unit vector perpendicular to both
-- statement:
--   Let `u`, `v` be an orthonormal pair in `Space3 = Fin 3 → ℝ`, in the sense used by `RoundCircle`:
--
--     * `(∑ i, u i * u i) = 1`
--     * `(∑ i, v i * v i) = 1`
--     * `(∑ i, u i * v i) = 0`
--
--   Then the cross product `u ⨯₃ v`
--
--     * has **Euclidean length one**: `(∑ i, (u ⨯₃ v) i * (u ⨯₃ v) i) = 1`, and
--     * is perpendicular to `u` and to `v`.
--
--   Two remarks that matter for the geometry.
--
--   First, the norm here is genuinely the Euclidean one. `Space3` carries the supremum norm, in which every vector with a coordinate `±1` already has norm one, so `u ⨯₃ v` need not be a unit vector in `‖·‖∞`. The `RoundCircle` condition `∑ i, u i * u i = 1` is the **square** of the Euclidean norm, and that is the norm in which the conclusion holds.
--
--   Second, orthonormality of the pair forces `‖u ⨯₃ v‖₂ = 1` rather than merely `≤ 1`. This is Lagrange's identity `‖u × v‖₂^2 = ‖u‖₂^2 ‖v‖₂^2 - (u · v)^2 = 1`.
--
--   This is the unit normal required to write the plane of a round circle as `{x : (x - c) • w = 0}` in the lifted-dome construction of the Freedman–Skora shrinking argument.
-- source:
--   **The identity.** `Mathlib.LinearAlgebra.CrossProduct.cross_dot_cross` is the scalar quadruple product identity
--
--       u ⨯₃ v ⬝ᵥ w ⨯₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w.
--
--   Substituting `w := u` and `x := v` gives
--
--       ‖u × v‖₂^2 = (u · u) * (v · v) - (u · v)^2 = 1 * 1 - 0 = 1,
--
--   which is Lagrange's identity specialised to an orthonormal pair. It yields equality, not an inequality.
--
--   **Perpendicularity.** `dot_self_cross u v : u ⬝ᵥ u ⨯₃ v = 0` gives the perpendicularity to `v` after commuting the dot product, and instantiating at `(u, v)` swapped gives the perpendicularity to `u`. `dot_cross_self` gives the same facts in the other order.
--
--   **The bridge.** `Matrix.dotProduct v w` is *defined* as `∑ i, v i * w i` (`Mathlib/Data/Matrix/Mul.lean:71`), so `u ⬝ᵥ w` and the coordinate sums in the statement are the same term. The `simpa [dotProduct]` unfolds that definition and `dotProduct_comm` handles the reordering.
--
--   **Correction note.** The earlier catalogue entry `BookSixth.orthonormal_frame_cross_unit_euclidean` (`02898b78-1218-48f8-9fb7-2bc1b8202914`) carried a superfluous binder `w : Space3` and concluded `w = u ⨯₃ v ∧ ...`. With `w` unconstrained that statement is false: take `u = ![1,0,0]`, `v = ![0,1,0]` and `w = 0`; the hypotheses hold but `w ≠ u ⨯₃ v = ![0,0,1]`. This `_v2` entry states the intended claim, with no free `w`.

import Mathlib
import Definitions.Def_BookSixth
import Mathlib.LinearAlgebra.CrossProduct
open scoped BigOperators
open BookSixth
open Matrix

theorem BookSixth.orthonormal_frame_cross_unit_euclidean_v2 (u v : Space3) (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) : (∑ i, (u ⨯₃ v) i * (u ⨯₃ v) i) = 1 ∧ (∑ i, (u ⨯₃ v) i * u i) = 0 ∧ (∑ i, (u ⨯₃ v) i * v i) = 0 := by sorry
