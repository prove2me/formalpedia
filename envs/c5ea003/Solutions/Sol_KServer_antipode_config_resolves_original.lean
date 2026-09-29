-- Prove2me | solution 1 for KServer.antipode_config_resolves_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T06:39:16.421666+00:00
-- url     : https://prove2.me/submissions/d568f855-898f-4de3-8420-c77b93877a92

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_mcshane_envelope
import Theorems.Thm_KServer_workFnU_mcshane_request

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

private theorem swap01' {N : Type} [MetricSpace N] (C₀ : Config 3 N) (σ : List N)
    (p q z : N) : workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![q, p, z] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 0 1) ?_
  intro i
  match i with
  | 0 => show p = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 0); rw [Equiv.swap_apply_left]; rfl
  | 1 => show q = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 1); rw [Equiv.swap_apply_right]; rfl
  | 2 => show z = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 2)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl

/-- **A configuration holding the request's antipode resolves through an original server.** -/
theorem solution (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r y z : M) :
    @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl z]
      = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl r, Sum.inl z]
        + dist y r
    ∨ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl z]
      = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl r]
        + dist z r := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := (σ ++ [r]).map Sum.inl with hτ
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have dLL : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inl b) = dist a b := fun _ _ => rfl
  have dLR : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inr b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  -- the two Lipschitz upper halves
  have hly : workFnU E₀ τ ![Sum.inr r, Sum.inl y, Sum.inl z]
      ≤ workFnU E₀ τ ![Sum.inr r, Sum.inl r, Sum.inl z] + dist y r := by
    have h := lip ![Sum.inr r, Sum.inl y, Sum.inl z] ![Sum.inr r, Sum.inl r, Sum.inl z]
    have hmc : moveCost (![Sum.inr r, Sum.inl r, Sum.inl z] : Config 3 (M ⊕ M))
        ![Sum.inr r, Sum.inl y, Sum.inl z] = dist y r := by
      rw [mc3]
      show dist r r + dist r y + dist z z = dist y r
      rw [dist_self, dist_self, dist_comm r y]
      ring
    rw [hmc] at h
    exact h
  have hlz : workFnU E₀ τ ![Sum.inr r, Sum.inl y, Sum.inl z]
      ≤ workFnU E₀ τ ![Sum.inr r, Sum.inl y, Sum.inl r] + dist z r := by
    have h := lip ![Sum.inr r, Sum.inl y, Sum.inl z] ![Sum.inr r, Sum.inl y, Sum.inl r]
    have hmc : moveCost (![Sum.inr r, Sum.inl y, Sum.inl r] : Config 3 (M ⊕ M))
        ![Sum.inr r, Sum.inl y, Sum.inl z] = dist z r := by
      rw [mc3]
      show dist r r + dist y y + dist r z = dist z r
      rw [dist_self, dist_self, dist_comm r z]
      ring
    rw [hmc] at h
    exact h
  -- expand through the envelope at an original configuration containing r
  obtain ⟨A, ⟨j, hAj⟩, hA⟩ := workFnU_mcshane_request 3 h3 M Δ hΔ0 hΔ C₀ σ r
    ![Sum.inr r, Sum.inl y, Sum.inl z]
  rw [← hτ] at hA
  have hmcA : @moveCost 3 (M ⊕ M) _ (fun i => Sum.inl (A i))
      ![Sum.inr r, Sum.inl y, Sum.inl z]
      = (2 * Δ - dist (A 0) r) + dist (A 1) y + dist (A 2) z := by
    rw [mc3]
    show dist (Sum.inl (A 0) : M ⊕ M) (Sum.inr r) + dist (Sum.inl (A 1) : M ⊕ M) (Sum.inl y)
        + dist (Sum.inl (A 2) : M ⊕ M) (Sum.inl z)
        = (2 * Δ - dist (A 0) r) + dist (A 1) y + dist (A 2) z
    rw [dLR, dLL, dLL]
  -- the ∀-half of the envelope, at any target and original configuration
  have hle : ∀ (Z : Config 3 (M ⊕ M)) (X : Config 3 M),
      workFnU E₀ τ Z ≤ workFnU C₀ (σ ++ [r]) X
        + @moveCost 3 (M ⊕ M) _ (fun i => Sum.inl (X i)) Z := by
    intro Z X
    have h := (workFnU_mcshane_envelope 3 h3 M Δ hΔ0 hΔ C₀ (σ ++ [r]) Z).1 X
    rw [← hτ] at h
    exact h
  match j, hAj with
  | ⟨1, _⟩, hAj =>
    left
    refine le_antisymm hly ?_
    have hb := hle ![Sum.inr r, Sum.inl r, Sum.inl z] A
    have hmcB : @moveCost 3 (M ⊕ M) _ (fun i => Sum.inl (A i))
        ![Sum.inr r, Sum.inl r, Sum.inl z]
        = (2 * Δ - dist (A 0) r) + dist (A 1) r + dist (A 2) z := by
      rw [mc3]
      show dist (Sum.inl (A 0) : M ⊕ M) (Sum.inr r) + dist (Sum.inl (A 1) : M ⊕ M) (Sum.inl r)
          + dist (Sum.inl (A 2) : M ⊕ M) (Sum.inl z)
          = (2 * Δ - dist (A 0) r) + dist (A 1) r + dist (A 2) z
      rw [dLR, dLL, dLL]
    rw [hmcB] at hb
    have h1 : A 1 = r := hAj
    have hd1 : dist (A 1) r = 0 := by rw [h1, dist_self]
    have hd2 : dist (A 1) y = dist y r := by rw [h1, dist_comm r y]
    rw [hA, hmcA]
    linarith
  | ⟨2, _⟩, hAj =>
    right
    refine le_antisymm hlz ?_
    have hb := hle ![Sum.inr r, Sum.inl y, Sum.inl r] A
    have hmcB : @moveCost 3 (M ⊕ M) _ (fun i => Sum.inl (A i))
        ![Sum.inr r, Sum.inl y, Sum.inl r]
        = (2 * Δ - dist (A 0) r) + dist (A 1) y + dist (A 2) r := by
      rw [mc3]
      show dist (Sum.inl (A 0) : M ⊕ M) (Sum.inr r) + dist (Sum.inl (A 1) : M ⊕ M) (Sum.inl y)
          + dist (Sum.inl (A 2) : M ⊕ M) (Sum.inl r)
          = (2 * Δ - dist (A 0) r) + dist (A 1) y + dist (A 2) r
      rw [dLR, dLL, dLL]
    rw [hmcB] at hb
    have h2 : A 2 = r := hAj
    have hd1 : dist (A 2) r = 0 := by rw [h2, dist_self]
    have hd2 : dist (A 2) z = dist z r := by rw [h2, dist_comm r z]
    rw [hA, hmcA]
    linarith
  | ⟨0, _⟩, hAj =>
    left
    refine le_antisymm hly ?_
    -- swap the first two coordinates of A so that r faces the middle slot
    have h0 : A 0 = r := hAj
    set A' : Config 3 M := ![A 1, A 0, A 2] with hA'
    have hwperm : workFnU C₀ (σ ++ [r]) A' = workFnU C₀ (σ ++ [r]) A := by
      have hAeta : A = ![A 0, A 1, A 2] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hA']
      conv_rhs => rw [hAeta]
      exact swap01' C₀ (σ ++ [r]) (A 1) (A 0) (A 2)
    have hb := hle ![Sum.inr r, Sum.inl r, Sum.inl z] A'
    have hmcB : @moveCost 3 (M ⊕ M) _ (fun i => Sum.inl (A' i))
        ![Sum.inr r, Sum.inl r, Sum.inl z]
        = (2 * Δ - dist (A 1) r) + dist (A 0) r + dist (A 2) z := by
      rw [mc3]
      show dist (Sum.inl (A 1) : M ⊕ M) (Sum.inr r) + dist (Sum.inl (A 0) : M ⊕ M) (Sum.inl r)
          + dist (Sum.inl (A 2) : M ⊕ M) (Sum.inl z)
          = (2 * Δ - dist (A 1) r) + dist (A 0) r + dist (A 2) z
      rw [dLR, dLL, dLL]
    rw [hmcB, hwperm] at hb
    have hd0 : dist (A 0) r = 0 := by rw [h0, dist_self]
    -- triangle: d(y,r) ≤ d(A 1, y) + d(A 1, r)
    have htri : dist y r ≤ dist (A 1) y + dist (A 1) r := by
      have h := dist_triangle y (A 1) r
      have hc : dist y (A 1) = dist (A 1) y := dist_comm y (A 1)
      linarith
    rw [hA, hmcA]
    linarith
