-- Prove2me | solution 1 for mme_recursive_thin_split_marginals_unique
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-11T22:10:06.838922+00:00
-- url     : https://prove2.me/submissions/2ca781c5-83b4-4574-88e0-e046cf11cb50

import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Tactic.FinCases

open BigOperators MME.RecursiveThinSplit

set_option autoImplicit false

private theorem event_sum {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (coord : A → I) (p : A → ℝ) (P : I → Prop) [DecidablePred P] :
    (∑ a, if P (coord a) then p a else 0) =
      ∑ j, if P j then mme_modern_marginal coord p j else 0 := by
  rw [← Fintype.sum_fiberwise coord (fun a ↦ if P (coord a) then p a else 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mme_modern_marginal]
  simp_rw [show ∀ a : {a // coord a = j}, coord a.val = j from fun a ↦ a.property]
  rw [Finset.sum_ite_irrel]
  simp

private theorem event_eq {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (coord : A → I) (p q : A → ℝ)
    (h : ∀ j, mme_modern_marginal coord p j = mme_modern_marginal coord q j)
    (P : I → Prop) [DecidablePred P] :
    (∑ a, if P (coord a) then p a else 0) =
      ∑ a, if P (coord a) then q a else 0 := by
  rw [event_sum coord p P, event_sum coord q P]
  apply Finset.sum_congr rfl
  intro j _
  rw [h j]

private theorem thin_plane_unique {A : Type*} [Fintype A] {half : ℕ}
    (x y z : A → Fin (half + 1))
    (separate : ∀ a b, x a = x b → y a = y b → z a = z b → a = b)
    (thin : ∀ a, (x a).val ≤ 1)
    (total : ∀ a, (x a).val + (y a).val + (z a).val = half)
    (p q : A → ℝ)
    (hy : ∀ j, mme_modern_marginal y p j = mme_modern_marginal y q j)
    (hz : ∀ j, mme_modern_marginal z p j = mme_modern_marginal z q j) : p = q := by
  classical
  funext a
  have ha := total a
  have hxa := thin a
  by_cases hx0 : (x a).val = 0
  · have reconstruct (w : A → ℝ) : w a =
        (∑ b, if (z a).val ≤ (z b).val then w b else 0) -
        ∑ b, if (y b).val < (y a).val then w b else 0 := by
      rw [← Finset.sum_sub_distrib]
      calc
        w a = ∑ b, if b = a then w b else 0 := by simp
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases heq : b = a
          · subst b; simp
          · have hb := total b
            have hxb := thin b
            have hne : ¬ ((x b).val = (x a).val ∧
                (y b).val = (y a).val ∧ (z b).val = (z a).val) := by
              rintro ⟨h1, h2, h3⟩
              exact heq (separate b a (Fin.ext h1) (Fin.ext h2) (Fin.ext h3))
            have iff_cut : ((z a).val ≤ (z b).val) ↔ ((y b).val < (y a).val) := by
              omega
            simp [heq, iff_cut]
    rw [reconstruct p, reconstruct q,
      event_eq z p q hz (fun j ↦ (z a).val ≤ j.val),
      event_eq y p q hy (fun j ↦ j.val < (y a).val)]
  · have hx1 : (x a).val = 1 := by omega
    have reconstruct (w : A → ℝ) : w a =
        (∑ b, if (y b).val ≤ (y a).val then w b else 0) -
        ∑ b, if (z a).val < (z b).val then w b else 0 := by
      rw [← Finset.sum_sub_distrib]
      calc
        w a = ∑ b, if b = a then w b else 0 := by simp
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases heq : b = a
          · subst b; simp
          · have hb := total b
            have hxb := thin b
            have hne : ¬ ((x b).val = (x a).val ∧
                (y b).val = (y a).val ∧ (z b).val = (z a).val) := by
              rintro ⟨h1, h2, h3⟩
              exact heq (separate b a (Fin.ext h1) (Fin.ext h2) (Fin.ext h3))
            have iff_cut : ((y b).val ≤ (y a).val) ↔ ((z a).val < (z b).val) := by
              omega
            simp [heq, iff_cut]
    rw [reconstruct p, reconstruct q,
      event_eq y p q hy (fun j ↦ j.val ≤ (y a).val),
      event_eq z p q hz (fun j ↦ (z a).val < j.val)]

theorem solution (half : ℕ) (parent : Fin 3 → ℕ)
    (hthin : ∃ i, parent i ≤ 1) (rho alpha : Split half parent → ℝ)
    (hmarg : ∀ (i : Fin 3) (j : Fin (half + 1)),
      mme_modern_marginal (fun a ↦ a.val i) rho j =
        mme_modern_marginal (fun a ↦ a.val i) alpha j) : rho = alpha := by
  classical
  obtain ⟨i, hi⟩ := hthin
  fin_cases i
  · apply thin_plane_unique (A := Split half parent) (fun a ↦ a.val 0) (fun a ↦ a.val 1) (fun a ↦ a.val 2)
      ?_ ?_ ?_ rho alpha (hmarg 1) (hmarg 2)
    · intro a b h0 h1 h2
      apply Subtype.ext; funext j; fin_cases j <;> assumption
    · intro a; exact (a.property.2 0).trans hi
    · intro a; exact a.property.1
  · apply thin_plane_unique (A := Split half parent) (fun a ↦ a.val 1) (fun a ↦ a.val 2) (fun a ↦ a.val 0)
      ?_ ?_ ?_ rho alpha (hmarg 2) (hmarg 0)
    · intro a b h1 h2 h0
      apply Subtype.ext; funext j; fin_cases j <;> assumption
    · intro a; exact (a.property.2 1).trans hi
    · intro a; have h := a.property.1; dsimp only; omega
  · apply thin_plane_unique (A := Split half parent) (fun a ↦ a.val 2) (fun a ↦ a.val 0) (fun a ↦ a.val 1)
      ?_ ?_ ?_ rho alpha (hmarg 0) (hmarg 1)
    · intro a b h2 h0 h1
      apply Subtype.ext; funext j; fin_cases j <;> assumption
    · intro a; exact (a.property.2 2).trans hi
    · intro a; have h := a.property.1; dsimp only; omega
