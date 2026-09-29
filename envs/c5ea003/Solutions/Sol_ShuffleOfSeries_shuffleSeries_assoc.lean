-- Prove2me | solution 1 for ShuffleOfSeries.shuffleSeries_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T03:27:39.945739+00:00
-- url     : https://prove2.me/submissions/2d0a3018-d0c1-4ed5-81c3-7a691d81ee5e

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Definitions.Def_Novelty_FreeMonoidCharacters
import Definitions.Def_Novelty_RepresentativeFunctions
import Definitions.Def_Novelty_ShuffleOfSeries

open ShuffleOfSeries FreeMonoidShuffle

open ShuffleOfSeries FreeMonoidShuffle in
/-- **The shuffle product of series is associative** (from coassociativity of `unsh`). -/
theorem solution {X K : Type*} [Field K] (f g h : List X → K) :
    shuffleSeries (shuffleSeries f g) h = shuffleSeries f (shuffleSeries g h) := by
  have coassoc : ∀ w : List X, coL w = coR w := by
    intro w
    induction w with
    | nil => simp [coL, coR, unsh]
    | cons a w ih =>
        have k : ∀ φ : List X × List X × List X → List X × List X × List X,
            (coL w).map φ = (coR w).map φ := fun φ => by rw [ih]
        have h1 := k (fun t => (a :: t.1, t.2.1, t.2.2))
        have h2 := k (fun t => (t.1, a :: t.2.1, t.2.2))
        have h3 := k (fun t => (t.1, t.2.1, a :: t.2.2))
        simp only [coL, coR, Multiset.map_bind, Multiset.map_map, Function.comp_def] at h1 h2 h3
        simp only [coL, coR, unsh, Multiset.add_bind, Multiset.bind_map, Multiset.map_add,
          Multiset.bind_add, Multiset.map_map, Function.comp_def]
        rw [h1, h2, h3, add_assoc]
  funext w
  have hL : shuffleSeries (shuffleSeries f g) h w
      = ((coL w).map (fun t => f t.1 * g t.2.1 * h t.2.2)).sum := by
    simp only [shuffleSeries, coL, Multiset.map_bind, Multiset.sum_bind, Multiset.map_map,
      Function.comp_def, Multiset.sum_map_mul_right]
  have hR : shuffleSeries f (shuffleSeries g h) w
      = ((coR w).map (fun t => f t.1 * g t.2.1 * h t.2.2)).sum := by
    simp only [shuffleSeries, coR, Multiset.map_bind, Multiset.sum_bind, Multiset.map_map,
      Function.comp_def, Multiset.sum_map_mul_left, mul_assoc]
  rw [hL, hR, coassoc]
