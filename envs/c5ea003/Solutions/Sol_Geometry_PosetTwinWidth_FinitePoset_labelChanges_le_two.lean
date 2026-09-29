-- Prove2me | solution 1 for Geometry.PosetTwinWidth.FinitePoset.labelChanges_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:19:51.861987+00:00
-- url     : https://prove2.me/submissions/fd59c38d-c723-4e94-b897-167a1b6fa147

import Mathlib
import Definitions.Def_Geometry_Contractions
import Definitions.Def_Geometry_PosetTheory_NonCircular
import Definitions.Def_Geometry_PosetTwinWidth_LinearBound
open Geometry.PosetTwinWidth Geometry.PosetTwinWidth.FinitePoset in
theorem solution (P : FinitePoset) (w : P.carrier) (l : List P.carrier)
    (hsorted : l.Pairwise (fun a b => P.le a b)) :
    labelChanges (P.label w) l ≤ 2 := by
  -- rank the labels `blue < green < red`
  obtain ⟨rk, hb, hg, hr⟩ : ∃ rk : Tri → ℕ, rk Tri.blue = 0 ∧ rk Tri.green = 1 ∧ rk Tri.red = 2 :=
    ⟨fun t => match t with
      | Tri.blue => 0
      | Tri.green => 1
      | Tri.red => 2, rfl, rfl, rfl⟩
  have hrk2 : ∀ t, rk t ≤ 2 := by
    intro t
    cases t <;> simp [hb, hg, hr]
  -- along `x ≤ y` the label can only move up: blue is down-closed, red is up-closed
  have hmono : ∀ x y, P.le x y → rk (P.label w x) ≤ rk (P.label w y) := by
    intro x y hxy
    unfold label
    by_cases h1 : P.le x w
    · simp only [h1, if_true, hb]
      exact Nat.zero_le _
    · have hy1 : ¬ P.le y w := fun h => h1 (P.le_trans hxy h)
      by_cases h2 : P.le w x
      · have hy2 : P.le w y := P.le_trans h2 hxy
        simp [h1, h2, hy1, hy2, hr]
      · simp only [h1, h2, hy1, if_false, hg]
        split_ifs <;> simp [hg, hr]
  have hstrict : ∀ s t : Tri, s ≠ t → rk s ≤ rk t → rk s < rk t := by
    intro s t hst hle
    cases s <;> cases t <;> simp_all
  have key : ∀ (a : P.carrier) (rest : List P.carrier),
      (a :: rest).Pairwise (fun a b => P.le a b) →
        labelChanges (P.label w) (a :: rest) + rk (P.label w a) ≤ 2 := by
    intro a rest
    induction rest generalizing a with
    | nil =>
      intro _
      simp [labelChanges, hrk2]
    | cons b rest ih =>
      intro hp
      have hab : P.le a b := List.rel_of_pairwise_cons hp (by simp)
      have ih' := ih b (List.Pairwise.of_cons hp)
      have hm := hmono a b hab
      simp only [labelChanges]
      by_cases heq : P.label w a = P.label w b
      · rw [if_pos heq, heq]
        omega
      · rw [if_neg heq]
        have := hstrict _ _ heq hm
        omega
  cases l with
  | nil => simp [labelChanges]
  | cons a rest =>
    have := key a rest hsorted
    omega
