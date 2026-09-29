-- Prove2me | solution 1 for KServer.anchor_push_case
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T07:20:08.143717+00:00
-- url     : https://prove2.me/submissions/0433d7a4-7078-4975-80b2-07c0d700f5b7

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_potential_push_first

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

/-- **The push case of the anchoring theorem**: if the first anchor (or its antipode)
resolves, the anchored potential is dominated by one anchored at the request last. -/
theorem solution (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r a b c : M)
    (h : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl a, Sum.inl b, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl r, Sum.inl b, Sum.inl c]
          + dist a r
      ∨ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr a, Sum.inl b, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl r, Sum.inl b, Sum.inl c]
          + (2 * Δ - dist a r)) :
    ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) b c r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b c
    ∨ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) c b r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b c := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := (σ ++ [r]).map Sum.inl with hτ
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  have hΦ : ∀ p q s : M, ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) p q s
      = workFnU E₀ τ ![Sum.inl p, Sum.inl q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr p, Sum.inl q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr q, Sum.inr q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr s, Sum.inr s, Sum.inr s] := fun p q s => rfl
  -- step 1: the anchored potential at (r, b, c) is dominated
  have hstep1 : ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) r b c
      ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b c := by
    rw [hΦ, hΦ]
    rcases h with h | h
    · -- original first anchor resolves
      have hlip1 : workFnU E₀ τ ![Sum.inr r, Sum.inl b, Sum.inl c]
          ≤ workFnU E₀ τ ![Sum.inr a, Sum.inl b, Sum.inl c] + dist a r := by
        have h2 := lip ![Sum.inr r, Sum.inl b, Sum.inl c] ![Sum.inr a, Sum.inl b, Sum.inl c]
        have hmc : moveCost (![Sum.inr a, Sum.inl b, Sum.inl c] : Config 3 (M ⊕ M))
            ![Sum.inr r, Sum.inl b, Sum.inl c] = dist a r := by
          rw [mc3]
          show dist a r + dist b b + dist c c = dist a r
          rw [dist_self, dist_self]
          ring
        rw [hmc] at h2
        exact h2
      linarith
    · -- the antipode of the first anchor resolves
      have hlip1 : workFnU E₀ τ ![Sum.inr r, Sum.inl b, Sum.inl c]
          ≤ workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl c] + (2 * Δ - dist a r) := by
        have h2 := lip ![Sum.inr r, Sum.inl b, Sum.inl c] ![Sum.inl a, Sum.inl b, Sum.inl c]
        have hmc : moveCost (![Sum.inl a, Sum.inl b, Sum.inl c] : Config 3 (M ⊕ M))
            ![Sum.inr r, Sum.inl b, Sum.inl c] = 2 * Δ - dist a r := by
          rw [mc3]
          show (2 * Δ - dist a r) + dist b b + dist c c = 2 * Δ - dist a r
          rw [dist_self, dist_self]
          ring
        rw [hmc] at h2
        exact h2
      linarith
  -- step 2: push the request from the first slot to the last
  have hpush := potential_push_first M Δ hΔ0 hΔ C₀ σ r b c
  have hperm1 : workFnU E₀ τ ![Sum.inl b, Sum.inl c, Sum.inl r]
      = workFnU E₀ τ ![Sum.inl r, Sum.inl b, Sum.inl c] :=
    rot3 E₀ τ (Sum.inl b) (Sum.inl c) (Sum.inl r)
  have hperm2 : workFnU E₀ τ ![Sum.inl c, Sum.inl b, Sum.inl r]
      = workFnU E₀ τ ![Sum.inl r, Sum.inl c, Sum.inl b] :=
    rot3 E₀ τ (Sum.inl c) (Sum.inl b) (Sum.inl r)
  have hperm3 : workFnU E₀ τ ![Sum.inl r, Sum.inl c, Sum.inl b]
      = workFnU E₀ τ ![Sum.inl r, Sum.inl b, Sum.inl c] := by
    refine perm3_eq E₀ τ _ _ (Equiv.swap 1 2) ?_
    intro i
    match i with
    | 0 => show (Sum.inl r : M ⊕ M)
             = ![Sum.inl r, Sum.inl b, Sum.inl c] ((Equiv.swap (1 : Fin 3) 2) 0)
           rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl
    | 1 => show (Sum.inl c : M ⊕ M)
             = ![Sum.inl r, Sum.inl b, Sum.inl c] ((Equiv.swap (1 : Fin 3) 2) 1)
           rw [Equiv.swap_apply_left]; rfl
    | 2 => show (Sum.inl b : M ⊕ M)
             = ![Sum.inl r, Sum.inl b, Sum.inl c] ((Equiv.swap (1 : Fin 3) 2) 2)
           rw [Equiv.swap_apply_right]; rfl
  rw [← hτ] at hpush
  rcases hpush with hp | hp
  · left
    refine le_trans ?_ hstep1
    rw [hΦ, hΦ]
    rw [hperm1]
    linarith
  · right
    refine le_trans ?_ hstep1
    rw [hΦ, hΦ]
    rw [hperm2, hperm3]
    linarith
