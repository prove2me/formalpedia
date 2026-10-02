-- Prove2me | solution 1 for BookSixth.orthonormal_frame_has_unit_cross_normal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T04:32:24.568831+00:00
-- url     : https://prove2.me/submissions/fb7a05e9-d1b0-4245-bfed-a7eab7209467

import Mathlib
import Definitions.Def_BookSixth
import Mathlib.LinearAlgebra.CrossProduct
open scoped BigOperators
open BookSixth
open Matrix

/-- **The cross product of an orthonormal frame is a Euclidean unit normal.**

For an orthonormal pair `u`, `v` in `Space3 = Fin 3 → ℝ` — in the sense used by
`RoundCircle`, so `(∑ i, u i * u i) = 1` and friends — there is a vector
`w := u ⨯₃ v` of Euclidean length one, perpendicular to both.

The norm is the genuine Euclidean one. `Space3` carries the supremum norm, in which
any vector with a coordinate `±1` already has norm one, so the `RoundCircle`
conditions are the square of the Euclidean norm rather than the supremum norm. The
conclusion `(∑ i, w i * w i) = 1` is exactly `‖w‖₂ ^ 2 = 1`.

Orthonormality of the pair forces the length to be *equal* to one, not merely at most
one: this is Lagrange's identity `‖u × v‖₂ ^ 2 = ‖u‖₂ ^ 2 ‖v‖₂ ^ 2 - (u · v)^2`.

This is the normal required to write the plane of a round circle as
`{x : (x - c) ⬝ᵥ w = 0}` in the lifted-dome construction underlying the
collision-free shrinking argument.

The statement is the existential one the original target text describes. The sibling
`BookSixth.orthonormal_frame_cross_unit_euclidean` (`02898b78`) binds `w` as an ordinary
theorem binder with no `∃`, so it asserts `w = u ⨯₃ v` for an arbitrary `w` and is refuted
by `u = e₀`, `v = e₁`, `w = e₀`. -/
theorem solution (u v : Space3) (hu : (∑ i, u i * u i) = 1)
    (hv : (∑ i, v i * v i) = 1) (huv : (∑ i, u i * v i) = 0) :
    ∃ w : Space3, w = u ⨯₃ v ∧ (∑ i, w i * w i) = 1 ∧
      (∑ i, w i * u i) = 0 ∧ (∑ i, w i * v i) = 0 := by
  -- The witness is the cross product itself, so the equation is `rfl`.  The
  -- accepted sibling `02898b78` reaches the same three goals via `subst w`; here
  -- the `∃` wrapper supplies the witness directly, and introducing it with
  -- `obtain`+`subst` instead would shadow the goal's own bound `w` and misalign
  -- the anonymous constructor, so `refine` is the right shape here.
  refine ⟨u ⨯₃ v, rfl, ?_, ?_, ?_⟩
  · -- Lagrange's identity specialised to the orthonormal pair:
    -- `‖u ⨯₃ v‖₂ ^ 2 = (u · u) * (v · v) - (u · v) * (v · u) = 1 * 1 - 0 * 0 = 1`.
    have h := cross_dot_cross u v u v
    have huv' : (∑ i, v i * u i) = 0 := by
      simpa [dotProduct, mul_comm] using huv
    simp only [dotProduct] at h
    rw [hu, hv, huv, huv'] at h
    simpa [dotProduct] using h
  · -- `u ⬝ᵥ (u ⨯₃ v) = 0`, and the goal is `(u ⨯₃ v) ⬝ᵥ u = 0`.
    --
    -- The sibling `02898b78` closes this with `simpa [dotProduct, dotProduct_comm]`,
    -- and that line is ACCEPTED (candidate 4015) — but only when `w` is a hypothesis
    -- binder discharged by `subst`.  Under this target's `∃` wrapper the identical
    -- line fails, and the recorded reason is ordering: `simp` applies the
    -- `dotProduct` unfolding *before* `dotProduct_comm` gets a chance, so `h`
    -- normalises to `∑ i, u i * (u ⨯₃ v) i = 0` while the goal is
    -- `∑ i, (u ⨯₃ v) i * u i = 0`, and the two never meet.
    --
    -- So: swap the factors with `rw` FIRST, while the term is still a `dotProduct`,
    -- and only then unfold.  `dotProduct (u ⨯₃ v) u` is *definitionally*
    -- `∑ i, (u ⨯₃ v) i * u i`, so `simpa only [dotProduct]` closes it.
    --
    -- `rw` rather than `simp` for the swap is essential: `rw` rewrites with the
    -- stated lemma exactly once, in the given order, whereas a `simp only` set
    -- containing both lemmas would be free to unfold `dotProduct` first and
    -- reach the same unmatchable `∑ i, u i * …` normal form that defeated
    -- candidates 4016, 4021 and 4033.
    have h := dot_self_cross u v
    rw [dotProduct_comm] at h
    simpa only [dotProduct] using h
  · -- `v ⬝ᵥ (u ⨯₃ v) = 0` against the goal `(u ⨯₃ v) ⬝ᵥ v = 0`, swapped the same way.
    have h := dot_cross_self u v
    rw [dotProduct_comm] at h
    simpa only [dotProduct] using h
