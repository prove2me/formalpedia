-- Prove2me | Theorems.Thm_BookSixth_orthonormal_frame_has_unit_cross_normal
-- name    : BookSixth.orthonormal_frame_has_unit_cross_normal
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T03:15:33.203041+00:00
-- url     : https://prove2.me/theorems/02c1fe73-3648-41aa-bb38-339f1740b729
-- title:
--   The cross product of an orthonormal frame is a Euclidean unit normal to that frame
-- statement:
--   Let `u`, `v` be an orthonormal pair in `Space3 = Fin 3 → ℝ` in the sense used by `RoundCircle`:
--
--   * `(∑ i, u i * u i) = 1`
--   * `(∑ i, v i * v i) = 1`
--   * `(∑ i, u i * v i) = 0`
--
--   Then there exists a vector `w` — namely `w := u ⨯₃ v` — such that `w` has Euclidean length one and is perpendicular to both `u` and `v`. Explicitly,
--
--   * `w = u ⨯₃ v`,
--   * `(∑ i, w i * w i) = 1`,
--   * `(∑ i, w i * u i) = 0`,
--   * `(∑ i, w i * v i) = 0`.
--
--   The norm is the genuine Euclidean one. `Space3` carries the supremum norm, in which any vector with a coordinate `±1` already has norm one, so the `RoundCircle` conditions are the square of the Euclidean norm `‖u‖₂` rather than `‖u‖∞`. The conclusion `(∑ i, w i * w i) = 1` is exactly `‖w‖₂ = 1`.
--
--   Orthonormality forces the length to be *equal* to one, not merely at most one: this is Lagrange's identity `‖u × v‖₂ ^ 2 = ‖u‖₂^2 ‖v‖₂^2 - (u · v)^2 = 1`.
--
--   This is the normal required to write the plane of a round circle as `{x : (x - c) ⬝ᵥ w = 0}` in the lifted-dome construction underlying the collision-free shrinking argument.
-- source:
--   **Why this restates the published target.** The already-published `BookSixth.orthonormal_frame_cross_unit_euclidean` (`02898b78-1218-48f8-9fb7-2bc1b8202914`) binds `w` as an ordinary theorem binder:
--
--       theorem BookSixth.orthonormal_frame_cross_unit_euclidean (u v w : Space3) (hu : …) (hv : …) (huv : …) :
--         w = u ⨯₃ v ∧ (∑ i, w i * w i) = 1 ∧ (∑ i, w i * u i) = 0 ∧ (∑ i, w i * v i) = 0
--
--   There is no `∃` and no `∀` in that type, so every binder is universally quantified and the statement asserts `w = u ⨯₃ v` for an *arbitrary* `w`. It is therefore refuted outright: take `u = e₀ = ![1,0,0]`, `v = e₁ = ![0,1,0]`, which satisfy all three hypotheses, and then supply the legal binder value `w = e₀`. The first conjunct demands `e₀ = e₀ ⨯₃ e₁ = e₂`, which is false. The remote CE `Tactic subst failed: did not find equation for eliminating 'w'` is exactly this defect surfacing: `w` is a free universal variable, so there is no defining equation to substitute.
--
--   The target's own `source` and `natural_language_statement` say "Then `w := u ⨯₃ v` is a unit vector", i.e. they describe an existential. This child states the faithful form, and the previously rejected proof body applies to it unchanged.
--
--   **The proof.** Take `w := u ⨯₃ v`, so the first conjunct is `rfl`. The length is Lagrange's identity, `cross_dot_cross u v u v : (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) * (v ⬝ᵥ u)`, whose right-hand side is `1 * 1 - 0 * 0 = 1` by `hu`, `hv` and `huv`. The two orthogonality relations are `dot_self_cross u v : u ⬝ᵥ (u ⨯₃ v) = 0` and `dot_cross_self u v : (u ⨯₃ v) ⬝ᵥ u = 0`, the second being the `u`-against-cross form; commutativity of the dot product turns the latter into `(∑ i, w i * u i) = 0`, and `dot_self_cross v u` together with `crossProduct v u = -(u ⨯₃ v)` gives the `v`-against-cross relation. All three declarations live in `Mathlib.LinearAlgebra.CrossProduct` at the pinned revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

import Mathlib
import Definitions.Def_BookSixth
import Mathlib.LinearAlgebra.CrossProduct
open scoped BigOperators
open BookSixth
open Matrix

theorem BookSixth.orthonormal_frame_has_unit_cross_normal (u v : Space3) (hu : (∑ i, u i * u i) = 1) (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) : ∃ w : Space3, w = u ⨯₃ v ∧ (∑ i, w i * w i) = 1 ∧ (∑ i, w i * u i) = 0 ∧ (∑ i, w i * v i) = 0 := by sorry
