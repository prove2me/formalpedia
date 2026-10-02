-- Prove2me | solution 1 for BookSixth.localized_similarity_isotopy_keeps_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T20:24:03.315148+00:00
-- url     : https://prove2.me/submissions/f5c7f148-56fd-43c0-a31e-87f674b53561

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_euclidean_isometry_preserves_roundness

noncomputable section

open scoped BigOperators
open BookSixth

/-- **Localised-similarity roundness: the missing glue between a per-component
motion and the leaf's fifth conjunct.**

This is the exact statement that any *localised* construction must deliver. It
asks only that at each time `t` the ambient map `K t` coincide, **on the
component `C i` itself**, with a positive scaling composed with an
inner-product-preserving linear map and a translation. The witness `(A, a, b)` is
allowed to depend on `(t, i)`, so different components are moved by *different*
similarities; no compatibility between the witnesses for different `i` is
required, and the witness is stated only *on* `C i`, not on all of `Space3`. That
locality is the whole point: `Set.image_congr` needs the two functions to agree
only on the set being mapped, so the global anisotropy of the ambient map is
irrelevant, exactly as the leaf needs.

Why this is the right shape, and why it is not the global statement: a single
global similarity per time is *impossible* for `m >= 2` with unequal radii
(diameter is scaled by `a`, `standardCircle j` has diameter exactly 2, so the
endpoint forces `a (1) = 1 / r i` simultaneously for every `i`). The
single-circle Proved theorem `70d16099` therefore cannot be reused verbatim for a
family; only its *local* form survives.

The proof is the roundness witness pushed through `Set.image_congr`; the
orthonormality and range identities are the two `hA` instances, exactly as in
`BookSixth.euclidean_isometry_preserves_roundness`. Nothing here is new
mathematics: this records which hypothesis is the load-bearing one. -/
theorem solution {m : ℕ} (C : Fin m → Set Space3) (K : ℝ → Space3 ≃ₜ Space3)
    (hround : ∀ i, RoundCircle (C i))
    (hom : ∀ t i, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : Space3,
      0 < a ∧ (∀ x y : Space3, (∑ k, (A x) k * (A y) k) = ∑ k, x k * y k) ∧
      ∀ x ∈ C i, K t x = a • (A x) + b) :
    ∀ t i, RoundCircle ((K t) '' C i) := by
  intro t i
  obtain ⟨A, a, b, ha, hA, hagree⟩ := hom t i
  have hEq : ((fun x : Space3 => a • (A x) + b) '' C i) = (K t) '' C i :=
    Set.image_congr (fun x hx => (hagree x hx).symm)
  rw [← hEq]
  exact BookSixth.euclidean_isometry_preserves_roundness (C i) A b a hA ha (hround i)
