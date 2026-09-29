-- Prove2me | solution 1 for SheafCohomologyRobustness.Nonabelian.nonabelian_isCoboundary_of_trivial_monodromy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:23:48.56778+00:00
-- url     : https://prove2.me/submissions/ec8c38fb-eaf7-45d6-a227-add0d31236fa

import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_NonabelianHolonomy
open SheafCohomologyRobustness GraphNerve Nonabelian in
theorem solution {ι : Type*} {G : Type*} [Group G] [Nonempty ι]
    {A : ι → ι → Prop} {c : ι → ι → G}
    (hsym : ∀ x y, A x y → A y x) (hinv : ∀ x y, c y x = (c x y)⁻¹)
    (hconn : IsConnectedNerve A) (hmon : TrivialMonodromy A c) :
    IsMulCoboundaryOn A c := by
  -- walk calculus: concatenation
  have L1 : ∀ (l m : List ι) (i : ι), endpt i (l ++ m) = endpt (endpt i l) m := by
    intro l m
    induction l with
    | nil => intro i; rfl
    | cons j t ih => intro i; exact ih j
  have L2 : ∀ (l m : List ι) (i : ι), wprod c i (l ++ m) = wprod c i l * wprod c (endpt i l) m := by
    intro l m
    induction l with
    | nil => intro i; simp [wprod, endpt]
    | cons j t ih =>
      intro i
      show c i j * wprod c j (t ++ m) = (c i j * wprod c j t) * wprod c (endpt j t) m
      rw [ih j, mul_assoc]
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
  have L6 : ∀ (l : List ι) (i : ι), wprod c (endpt i l) (revW i l) = (wprod c i l)⁻¹ := by
    intro l
    induction l with
    | nil => intro i; simp [wprod, revW]
    | cons j t ih =>
      intro i
      show wprod c (endpt j t) (revW j t ++ [i]) = (c i j * wprod c j t)⁻¹
      rw [L2, ih j, L5 t j]
      simp only [wprod, mul_one, hinv j i, mul_inv_rev, inv_inv]
  -- transport from a base region along chosen walks
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  choose L hL using hconn i₀
  -- path independence: two walks from `i₀` with the same end have the same monodromy
  have key' : ∀ (l m : List ι), IsWalk A i₀ l → IsWalk A i₀ m → endpt i₀ l = endpt i₀ m →
      wprod c i₀ l = wprod c i₀ m := by
    intro l m hl hm hlm
    have hw : IsWalk A i₀ (l ++ revW i₀ m) := by
      rw [L3, hlm]
      exact ⟨hl, L4 _ _ hm⟩
    have hclosed : endpt i₀ (l ++ revW i₀ m) = i₀ := by
      rw [L1, hlm, L5]
    have h1 := hmon i₀ _ hw hclosed
    rw [L2, hlm, L6] at h1
    exact mul_inv_eq_one.mp h1
  refine ⟨fun j => wprod c i₀ (L j), fun i j hij => ?_⟩
  have hwalk : IsWalk A i₀ (L i ++ [j]) := by
    rw [L3, (hL i).2]
    exact ⟨(hL i).1, hij, trivial⟩
  have hend : endpt i₀ (L i ++ [j]) = endpt i₀ (L j) := by
    rw [L1, (hL i).2, (hL j).2]
    rfl
  have := key' _ _ hwalk (hL j).1 hend
  rw [L2, (hL i).2] at this
  simp only [wprod, mul_one] at this
  show c i j = (wprod c i₀ (L i))⁻¹ * wprod c i₀ (L j)
  rw [← this]
  group
