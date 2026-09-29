-- Prove2me | solution 1 for KServer.antipode_coord_eval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T06:55:14.562124+00:00
-- url     : https://prove2.me/submissions/6771df72-2cb6-4b0f-9895-45dce270ca09

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_mcshane_envelope
import Theorems.Thm_KServer_workFnU_antipodal_extension_restrict

open KServer

variable {N : Type} [MetricSpace N]

private theorem perm3_eq (C₀ : Config 3 N) (σ : List N) (X Y : Config 3 N)
    (τ : Equiv.Perm (Fin 3)) (h : ∀ i, X i = Y (τ i)) :
    workFnU C₀ σ X = workFnU C₀ σ Y := by
  rw [show X = Y ∘ (τ : Equiv.Perm (Fin 3)) from funext h]
  exact workFnU_perm 3 N C₀ σ Y τ

private theorem swap12 (C₀ : Config 3 N) (σ : List N) (p q z : N) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![p, z, q] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 1 2) ?_
  intro i
  match i with
  | 0 => show p = ![p, z, q] ((Equiv.swap (1 : Fin 3) 2) 0)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl
  | 1 => show q = ![p, z, q] ((Equiv.swap (1 : Fin 3) 2) 1); rw [Equiv.swap_apply_left]; rfl
  | 2 => show z = ![p, z, q] ((Equiv.swap (1 : Fin 3) 2) 2); rw [Equiv.swap_apply_right]; rfl

private theorem rot3 (C₀ : Config 3 N) (σ : List N) (p q z : N) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![z, p, q] := by
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  have c0 : c 0 = 1 := by rw [hc]; decide
  have c1 : c 1 = 2 := by rw [hc]; decide
  have c2 : c 2 = 0 := by rw [hc]; decide
  refine perm3_eq C₀ σ _ _ c ?_
  intro i
  match i with
  | 0 => show p = ![z, p, q] (c 0); rw [c0]; rfl
  | 1 => show q = ![z, p, q] (c 1); rw [c1]; rfl
  | 2 => show z = ![z, p, q] (c 2); rw [c2]; rfl

private theorem mc3 (A B : Config 3 N) :
    moveCost A B = dist (A 0) (B 0) + dist (A 1) (B 1) + dist (A 2) (B 2) := by
  unfold moveCost
  rw [Fin.sum_univ_three]

/-- **Antipodal coordinates evaluate through original points.** -/
theorem solution (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (x y c : M) :
    (∃ u : M,
      @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x, Sum.inl y, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inl u, Sum.inl y, Sum.inl c]
          + (2 * Δ - dist u x))
    ∧ (∃ u v : M,
      @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x, Sum.inr y, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inl u, Sum.inl v, Sum.inl c]
          + ((2 * Δ - dist u x) + (2 * Δ - dist v y))) := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := σ.map Sum.inl with hτ
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  -- restriction: embedded original triples carry the original work function
  have hres : ∀ a b c' : M,
      workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl c'] = workFnU C₀ σ ![a, b, c'] := by
    intro a b c'
    have h := workFnU_antipodal_extension_restrict 3 h3 M Δ hΔ0 hΔ C₀ σ ![a, b, c']
    have hemb : (fun i => Sum.inl ((![a, b, c'] : Config 3 M) i) : Config 3 (M ⊕ M))
        = ![Sum.inl a, Sum.inl b, Sum.inl c'] := by
      funext l
      match l with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    rw [hemb] at h
    rw [← hτ] at h
    exact h
  constructor
  · -- one antipodal coordinate
    obtain ⟨-, A, hA⟩ := workFnU_mcshane_envelope 3 h3 M Δ hΔ0 hΔ C₀ σ
      ![Sum.inr x, Sum.inl y, Sum.inl c]
    rw [← hτ] at hA
    have hmcA : @moveCost 3 (M ⊕ M) _ (fun i => Sum.inl (A i))
        ![Sum.inr x, Sum.inl y, Sum.inl c]
        = (2 * Δ - dist (A 0) x) + dist (A 1) y + dist (A 2) c := by
      rw [mc3]
      rfl
    refine ⟨A 0, le_antisymm ?_ ?_⟩
    · -- Lipschitz upper bound
      have h := lip ![Sum.inr x, Sum.inl y, Sum.inl c] ![Sum.inl (A 0), Sum.inl y, Sum.inl c]
      have hmc : moveCost (![Sum.inl (A 0), Sum.inl y, Sum.inl c] : Config 3 (M ⊕ M))
          ![Sum.inr x, Sum.inl y, Sum.inl c] = 2 * Δ - dist (A 0) x := by
        rw [mc3]
        show (2 * Δ - dist (A 0) x) + dist y y + dist c c = 2 * Δ - dist (A 0) x
        rw [dist_self, dist_self]
        ring
      rw [hmc] at h
      exact h
    · -- attained via the envelope minimizer
      have hMlip : workFnU C₀ σ ![A 0, y, c] ≤ workFnU C₀ σ A
          + (dist (A 1) y + dist (A 2) c) := by
        have h := workFnU_lipschitz 3 h3 M C₀ σ ![A 0, y, c] A
        have hmc : moveCost A (![A 0, y, c] : Config 3 M)
            = dist (A 1) y + dist (A 2) c := by
          rw [mc3]
          show dist (A 0) (A 0) + dist (A 1) y + dist (A 2) c
              = dist (A 1) y + dist (A 2) c
          rw [dist_self]
          ring
        rw [hmc] at h
        exact h
      rw [hres (A 0) y c, hA, hmcA]
      linarith
  · -- two antipodal coordinates
    obtain ⟨-, A, hA⟩ := workFnU_mcshane_envelope 3 h3 M Δ hΔ0 hΔ C₀ σ
      ![Sum.inr x, Sum.inr y, Sum.inl c]
    rw [← hτ] at hA
    have hmcA : @moveCost 3 (M ⊕ M) _ (fun i => Sum.inl (A i))
        ![Sum.inr x, Sum.inr y, Sum.inl c]
        = (2 * Δ - dist (A 0) x) + (2 * Δ - dist (A 1) y) + dist (A 2) c := by
      rw [mc3]
      rfl
    refine ⟨A 0, A 1, le_antisymm ?_ ?_⟩
    · have h := lip ![Sum.inr x, Sum.inr y, Sum.inl c]
        ![Sum.inl (A 0), Sum.inl (A 1), Sum.inl c]
      have hmc : moveCost (![Sum.inl (A 0), Sum.inl (A 1), Sum.inl c] : Config 3 (M ⊕ M))
          ![Sum.inr x, Sum.inr y, Sum.inl c]
          = (2 * Δ - dist (A 0) x) + (2 * Δ - dist (A 1) y) := by
        rw [mc3]
        show (2 * Δ - dist (A 0) x) + (2 * Δ - dist (A 1) y) + dist c c
            = (2 * Δ - dist (A 0) x) + (2 * Δ - dist (A 1) y)
        rw [dist_self]
        ring
      rw [hmc] at h
      linarith
    · have hMlip : workFnU C₀ σ ![A 0, A 1, c] ≤ workFnU C₀ σ A + dist (A 2) c := by
        have h := workFnU_lipschitz 3 h3 M C₀ σ ![A 0, A 1, c] A
        have hmc : moveCost A (![A 0, A 1, c] : Config 3 M) = dist (A 2) c := by
          rw [mc3]
          show dist (A 0) (A 0) + dist (A 1) (A 1) + dist (A 2) c = dist (A 2) c
          rw [dist_self, dist_self]
          ring
        rw [hmc] at h
        exact h
      rw [hres (A 0) (A 1) c, hA, hmcA]
      linarith
