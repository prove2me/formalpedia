-- Prove2me | solution 1 for BookSixth.round_circle_single_standardize_keeps_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T13:55:49.185671+00:00
-- url     : https://prove2.me/submissions/22ea7802-a43d-4395-a4c9-2ab49ffa6638

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_standardizing_time_maps_are_similarities

noncomputable section

open scoped BigOperators
open BookSixth

set_option maxHeartbeats 2000000

/-- **Roundness at every time of the single-circle standardising isotopy.**

The first four conjuncts are exactly `BookSixth.standardizing_time_maps_are_similarities`
(target `70d16099`, Proved as candidate 3727), which is strictly stronger than this
target: it also states the pointwise form of every time map.  That extra
hypothesis is what discharges the fifth conjunct here.

The parent gives, for each `t`, witnesses `A a b` with `0 < a`, with `A` preserving
`∑ i, x i * y i`, and with `K t x = a • (A x) + b`.  Pushing that through the
`RoundCircle` witness for `D`, whose centre is `c`, orthonormal frame `u, v` and
radius `r > 0`, produces the new witness

  centre `a • (A c) + b`,  frame `A u, A v`,  radius `a * r`.

The three orthonormal equations are the parent's hypothesis instantiated at
`(u, u)`, `(v, v)` and `(u, v)`; nothing new is proved about `A`.  The image
identity is the parent's pointwise equation at the round parametrisation, whose
left-hand side is expanded by `map_add`/`map_smul` and closed by `module`.

`BookSixth.similarity_preserves_roundness` is deliberately not used: it covers
only `x ↦ a • x + b` and cannot see the `A x` in the middle. -/
theorem solution (D : Set Space3) (hroundD : RoundCircle D) (k : ℕ) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (K 1) '' D = standardCircle k ∧
      (∀ t, RoundCircle ((K t) '' D)) := by
  obtain ⟨K, hK1, hK2, hK0, hKD, hKpt⟩ :=
    BookSixth.standardizing_time_maps_are_similarities D hroundD k
  refine ⟨K, hK1, hK2, hK0, hKD, ?_⟩
  -- Skolemise the parent's `∀ t, ∃ A a b, ...` so the witnesses become functions
  -- of `t` and the specification stays pointwise.
  choose A a b hpos hIP hpt using hKpt
  intro t
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hD⟩ := hroundD
  refine ⟨a t • (A t c) + b t, A t u, A t v, a t * r, mul_pos (hpos t) hr, ?_, ?_, ?_, ?_⟩
  · have h := hIP t u u
    simpa only [show (∑ i, u i * u i) = (∑ i, (A t u) i * (A t u) i) from h.symm] using h.trans hu
  · have h := hIP t v v
    simpa only [show (∑ i, v i * v i) = (∑ i, (A t v) i * (A t v) i) from h.symm] using h.trans hv
  · have h := hIP t u v
    simpa only [show (∑ i, u i * v i) = (∑ i, (A t u) i * (A t v) i) from h.symm] using h.trans huv
  · have key : ∀ s : ℝ, (K t) (c + (r * Real.cos s) • u + (r * Real.sin s) • v)
        = (a t • (A t c) + b t) + (a t * r * Real.cos s) • (A t u)
          + (a t * r * Real.sin s) • (A t v) := by
      intro s
      have hpt := hpt t (c + (r * Real.cos s) • u + (r * Real.sin s) • v)
      rw [hpt]
      simp only [map_add, map_smul, smul_add, smul_smul]
      module
    rw [hD, ← Set.image_univ, Set.image_image, ← Set.image_univ, Set.image_congr]
    intro y _
    exact key y
