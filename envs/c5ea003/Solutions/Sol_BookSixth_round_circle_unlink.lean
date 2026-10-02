-- Prove2me | solution 1 for BookSixth.round_circle_unlink
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T21:01:38.748991+00:00
-- url     : https://prove2.me/submissions/f7de3873-0b6b-44f1-b95e-af7885bab133
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_round_circle_unlink_empty
import Theorems.Thm_BookSixth_round_circle_unlink_snoc

open scoped BigOperators
open BookSixth

theorem solution {m : ℕ} (C : Fin m → Set Space3)
    (hround : ∀ i, RoundCircle (C i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hpairs : ∀ i j, i ≠ j → IsUnlink (![C i, C j] : Fin 2 → Set Space3)) :
    IsUnlink C := by
  classical
  induction m with
  | zero =>
      have hC : C = (fun _ : Fin 0 => (∅ : Set Space3)) := by
        funext i
        exact Fin.elim0 i
      rw [hC]
      exact BookSixth.round_circle_unlink_empty
  | succ n ih =>
      let C₀ : Fin n → Set Space3 := fun i => C i.castSucc
      have hroundC₀ : ∀ i, RoundCircle (C₀ i) := by
        intro i
        exact hround i.castSucc
      have hdisjointC₀ : ∀ i j, i ≠ j → Disjoint (C₀ i) (C₀ j) := by
        intro i j hij
        apply hdisjoint i.castSucc j.castSucc
        intro h
        apply hij
        exact Fin.castSucc_injective n h
      have hdisjointD : ∀ i, Disjoint (C₀ i) (C (Fin.last n)) := by
        intro i
        apply hdisjoint i.castSucc (Fin.last n)
        simp
      have hpairsD : ∀ i, IsUnlink (![C₀ i, C (Fin.last n)] : Fin 2 → Set Space3) := by
        intro i
        apply hpairs i.castSucc (Fin.last n)
        simp
      have hprefix : IsUnlink C₀ := by
        apply ih C₀ hroundC₀ hdisjointC₀
        intro i j hij
        apply hpairs i.castSucc j.castSucc
        intro h
        exact hij (Fin.castSucc_injective n h)
      have hs := BookSixth.round_circle_unlink_snoc C₀ (C (Fin.last n))
        hroundC₀ (hround (Fin.last n)) hdisjointC₀ hdisjointD hprefix hpairsD
      have hC : Fin.snoc C₀ (C (Fin.last n)) = C := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [C₀]
        · simp [C₀]
      rw [hC] at hs
      exact hs
