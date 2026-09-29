-- Prove2me | solution 1 for SheafCohomologyRobustness.GraphNerve.isCoboundary_of_cycleConsistent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:18:19.653483+00:00
-- url     : https://prove2.me/submissions/32a11102-0664-4990-a014-04f524bed904

import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
open SheafCohomologyRobustness GraphNerve in
theorem solution {ι : Type*} {M : Type*} [AddCommGroup M] [Nonempty ι] {A : ι → ι → Prop}
    {c : ι → ι → M}
    (hsym : ∀ x y, A x y → A y x) (hanti : ∀ x y, c y x = - c x y)
    (hconn : IsConnectedNerve A) (hcyc : CycleConsistent A c) : IsCoboundaryOn A c := by
  -- walk calculus: concatenation
  have L1 : ∀ (l m : List ι) (i : ι), endpt i (l ++ m) = endpt (endpt i l) m := by
    intro l m
    induction l with
    | nil => intro i; rfl
    | cons j t ih => intro i; exact ih j
  have L2 : ∀ (l m : List ι) (i : ι), wsum c i (l ++ m) = wsum c i l + wsum c (endpt i l) m := by
    intro l m
    induction l with
    | nil => intro i; simp [wsum, endpt]
    | cons j t ih =>
      intro i
      show c i j + wsum c j (t ++ m) = (c i j + wsum c j t) + wsum c (endpt j t) m
      rw [ih j, add_assoc]
  have L3 : ∀ (l m : List ι) (i : ι),
      IsWalk A i (l ++ m) ↔ IsWalk A i l ∧ IsWalk A (endpt i l) m := by
    intro l m
    induction l with
    | nil => intro i; simp [IsWalk, endpt]
    | cons j t ih =>
      intro i
      show (A i j ∧ IsWalk A j (t ++ m)) ↔ (A i j ∧ IsWalk A j t) ∧ IsWalk A (endpt j t) m
      rw [ih j, and_assoc]
  -- walk calculus: reversal
  have L5 : ∀ (l : List ι) (i : ι), endpt (endpt i l) (revW i l) = i := by
    intro l
    cases l with
    | nil => intro i; rfl
    | cons j t =>
      intro i
      show endpt (endpt j t) (revW j t ++ [i]) = i
      rw [L1]
      rfl
  have L4 : ∀ (l : List ι) (i : ι), IsWalk A i l → IsWalk A (endpt i l) (revW i l) := by
    intro l
    induction l with
    | nil => intro i _; trivial
    | cons j t ih =>
      rintro i ⟨hij, ht⟩
      show IsWalk A (endpt j t) (revW j t ++ [i])
      rw [L3, L5 t j]
      exact ⟨ih j ht, hsym i j hij, trivial⟩
  have L6 : ∀ (l : List ι) (i : ι), wsum c (endpt i l) (revW i l) = - wsum c i l := by
    intro l
    induction l with
    | nil => intro i; simp [wsum, revW]
    | cons j t ih =>
      intro i
      show wsum c (endpt j t) (revW j t ++ [i]) = - (c i j + wsum c j t)
      rw [L2, ih j, L5 t j]
      simp only [wsum, add_zero, hanti j i]
      abel
  -- integrate from a base region along chosen walks
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  choose L hL using hconn i₀
  -- path independence: two walks from `i₀` with the same end have the same holonomy
  have key' : ∀ (l m : List ι), IsWalk A i₀ l → IsWalk A i₀ m → endpt i₀ l = endpt i₀ m →
      wsum c i₀ l = wsum c i₀ m := by
    intro l m hl hm hlm
    have hw : IsWalk A i₀ (l ++ revW i₀ m) := by
      rw [L3, hlm]
      exact ⟨hl, L4 _ _ hm⟩
    have hclosed : endpt i₀ (l ++ revW i₀ m) = i₀ := by
      rw [L1, hlm, L5]
    have h0 := hcyc i₀ _ hw hclosed
    rw [L2, hlm, L6] at h0
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h0)
  have key : ∀ (l : List ι) (j : ι), IsWalk A i₀ l → endpt i₀ l = j →
      wsum c i₀ l = wsum c i₀ (L j) := by
    intro l j hl hj
    exact key' l (L j) hl (hL j).1 (by rw [hj, (hL j).2])
  refine ⟨fun j => wsum c i₀ (L j), fun i j hij => ?_⟩
  have hwalk : IsWalk A i₀ (L i ++ [j]) := by
    rw [L3, (hL i).2]
    exact ⟨(hL i).1, hij, trivial⟩
  have hend : endpt i₀ (L i ++ [j]) = j := by rw [L1]; rfl
  have := key _ j hwalk hend
  rw [L2, (hL i).2] at this
  simp only [wsum, add_zero] at this
  show c i j = wsum c i₀ (L j) - wsum c i₀ (L i)
  rw [← this]
  abel
