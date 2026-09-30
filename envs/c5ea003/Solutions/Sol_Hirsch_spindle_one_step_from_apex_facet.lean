-- Prove2me | solution 1 for Hirsch.spindle_one_step_from_apex_facet
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T15:01:28.229326+00:00
-- url     : https://prove2.me/submissions/8af0ec2c-8141-46ed-9b77-06f28dd70806

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_spindle_normalize
import Theorems.Thm_Hirsch_spindle_one_step_axis

open scoped RealInnerProductSpace
open Set Hirsch

theorem solution (d n : ℕ) (hd : 0 < d) (hn : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) (i0 : Fin n)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (htight : ⟪a i0, u⟫ = b i0)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)))
      (b' : Fin (n + 1) → ℝ)
      (u' v' : EuclideanSpace ℝ (Fin (d + 1))),
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      u' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      v' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      (∀ i, (⟪a' i, u'⟫ = b' i) ↔ ⟪a' i, v'⟫ ≠ b' i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin (d + 1)),
        ¬ (w 0 = u' ∧ w (d + 1) = v' ∧
            ∀ j < d + 1, w j = w (j + 1) ∨
              Adj (Hpoly a' b') (w j) (w (j + 1))) := by
  obtain ⟨aN, bN, hneN, hbdN, huN, hvN, hspN, htightN, hlongN⟩ :=
    spindle_normalize d n hd a b u v hne hbd hu hv hspindle hlong
  have ht : ⟪aN i0, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = bN i0 :=
    (htightN i0).1 htight
  exact spindle_one_step_axis d n hd hn aN bN i0 hneN hbdN huN hvN hspN ht hlongN
