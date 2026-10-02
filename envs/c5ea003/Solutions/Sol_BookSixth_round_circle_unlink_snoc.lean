-- Prove2me | solution 1 for BookSixth.round_circle_unlink_snoc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T21:31:44.181848+00:00
-- url     : https://prove2.me/submissions/7215e930-4235-4af3-9440-d3b6e0451cba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_round_circle_snoc_transport
import Theorems.Thm_BookSixth_round_circle_snoc_of_transport

open scoped BigOperators
open BookSixth

theorem solution {n : ℕ} (C : Fin n → Set Space3) (D : Set Space3)
    (hroundC : ∀ i, RoundCircle (C i)) (hroundD : RoundCircle D)
    (hdisjointC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hdisjointD : ∀ i, Disjoint (C i) D)
    (hprefix : IsUnlink C)
    (hpairs : ∀ i, IsUnlink (![C i, D] : Fin 2 → Set Space3)) :
    IsUnlink (Fin.snoc C D) := by
  apply BookSixth.round_circle_snoc_of_transport C D
  apply BookSixth.round_circle_snoc_transport C D hroundC hroundD
    hdisjointC hdisjointD hprefix hpairs
