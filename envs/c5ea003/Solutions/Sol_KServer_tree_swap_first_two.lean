-- Prove2me | solution 1 for KServer.tree_swap_first_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T07:05:56.47527+00:00
-- url     : https://prove2.me/submissions/8f53f234-188b-4035-8aeb-754d600d3a58

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_tree_metric
import Definitions.Def_KServer_ck_potential
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_antipodal_extension_restrict
import Theorems.Thm_KServer_antipode_coord_eval
import Theorems.Thm_KServer_workFnU_dual_pair_exchange
import Theorems.Thm_KServer_tree_one_server_potential_minimizer
import Theorems.Thm_KServer_potential_anchor_swap

open KServer

variable {N : Type} [MetricSpace N]

private theorem perm3_eq (C₀ : Config 3 N) (σ : List N) (X Y : Config 3 N)
    (τ : Equiv.Perm (Fin 3)) (h : ∀ i, X i = Y (τ i)) :
    workFnU C₀ σ X = workFnU C₀ σ Y := by
  rw [show X = Y ∘ (τ : Equiv.Perm (Fin 3)) from funext h]
  exact workFnU_perm 3 N C₀ σ Y τ

private theorem rot3 (C₀ : Config 3 N) (σ : List N) (p q c : N) :
    workFnU C₀ σ ![p, q, c] = workFnU C₀ σ ![c, p, q] := by
  set e : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with he
  have e0 : e 0 = 1 := by rw [he]; decide
  have e1 : e 1 = 2 := by rw [he]; decide
  have e2 : e 2 = 0 := by rw [he]; decide
  refine perm3_eq C₀ σ _ _ e ?_
  intro i
  match i with
  | 0 => show p = ![c, p, q] (e 0); rw [e0]; rfl
  | 1 => show q = ![c, p, q] (e 1); rw [e1]; rfl
  | 2 => show c = ![c, p, q] (e 2); rw [e2]; rfl

private theorem swap12 (C₀ : Config 3 N) (σ : List N) (p q c : N) :
    workFnU C₀ σ ![p, q, c] = workFnU C₀ σ ![p, c, q] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 1 2) ?_
  intro i
  match i with
  | 0 => show p = ![p, c, q] ((Equiv.swap (1 : Fin 3) 2) 0)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl
  | 1 => show q = ![p, c, q] ((Equiv.swap (1 : Fin 3) 2) 1); rw [Equiv.swap_apply_left]; rfl
  | 2 => show c = ![p, c, q] ((Equiv.swap (1 : Fin 3) 2) 2); rw [Equiv.swap_apply_right]; rfl

private theorem mc3 (A B : Config 3 N) :
    moveCost A B = dist (A 0) (B 0) + dist (A 1) (B 1) + dist (A 2) (B 2) := by
  unfold moveCost
  rw [Fin.sum_univ_three]

/-- **Coester–Koutsoupias, Lemma 25, for three servers**: a minimizing anchor triple
can be chosen swap-symmetric in its first two anchors, with the doubled antipode of
the second anchor resolving to the first. -/
theorem solution (M : Type) [MetricSpace M] [Fintype M] [Nonempty M]
    (hM : IsTreeVertexSpace M) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ u v : M, dist u v ≤ Δ)
    (C₀ : Config 3 M) (σ : List M) :
    ∃ x₁ x₂ x₃ : M,
      ckPot M Δ hΔ0 hΔ C₀ σ = ckPotAt M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃
      ∧ ckPotAt M Δ hΔ0 hΔ C₀ σ x₂ x₁ x₃ = ckPotAt M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃
      ∧ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
          + (2 * Δ - dist x₁ x₂) := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := σ.map Sum.inl with hτ
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  -- restriction to the base space
  have hres3 : ∀ a b c : M,
      workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl c] = workFnU C₀ σ ![a, b, c] := by
    intro a b c
    have h := workFnU_antipodal_extension_restrict 3 h3 M Δ hΔ0 hΔ C₀ σ ![a, b, c]
    have hemb : (fun i => Sum.inl ((![a, b, c] : Config 3 M) i) : Config 3 (M ⊕ M))
        = ![Sum.inl a, Sum.inl b, Sum.inl c] := by
      funext l
      match l with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    rw [hemb] at h
    rw [← hτ] at h
    exact h
  -- ckPotAt unfolded
  have hΦ : ∀ a b c : M, ckPotAt M Δ hΔ0 hΔ C₀ σ a b c
      = workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl c]
        + workFnU E₀ τ ![Sum.inr a, Sum.inl b, Sum.inl c]
        + workFnU E₀ τ ![Sum.inr b, Sum.inr b, Sum.inl c]
        + workFnU E₀ τ ![Sum.inr c, Sum.inr c, Sum.inr c] := fun a b c => rfl
  -- step 1: a global minimizing triple
  obtain ⟨y₁, x₂, x₃, hy⟩ := exists_ckPot_eq M Δ hΔ0 hΔ C₀ σ
  have hymin : ∀ a b c : M, ckPotAt M Δ hΔ0 hΔ C₀ σ y₁ x₂ x₃ ≤ ckPotAt M Δ hΔ0 hΔ C₀ σ a b c :=
    fun a b c => hy ▸ ckPot_le M Δ hΔ0 hΔ C₀ σ a b c
  -- step 2: choose the first anchor greedily for the dual functional
  set v : M → ℝ := fun u => workFnU C₀ σ ![u, x₂, x₃] with hv
  obtain ⟨x₁, hx₁⟩ := Finite.exists_min (fun u : M => v u - dist x₂ u)
  refine ⟨x₁, x₂, x₃, ?_⟩
  -- Lipschitz collapse of an antipodal first coordinate (the ∀-side of coord-eval)
  have hlipA : ∀ (t : M) (z : M),
      workFnU E₀ τ ![Sum.inr t, Sum.inl x₂, Sum.inl x₃]
        ≤ workFnU E₀ τ ![Sum.inl z, Sum.inl x₂, Sum.inl x₃] + (2 * Δ - dist z t) := by
    intro t z
    have h := lip ![Sum.inr t, Sum.inl x₂, Sum.inl x₃] ![Sum.inl z, Sum.inl x₂, Sum.inl x₃]
    have hmc : moveCost (![Sum.inl z, Sum.inl x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
        ![Sum.inr t, Sum.inl x₂, Sum.inl x₃] = 2 * Δ - dist z t := by
      rw [mc3]
      show (2 * Δ - dist z t) + dist x₂ x₂ + dist x₃ x₃ = 2 * Δ - dist z t
      rw [dist_self, dist_self]
      ring
    rw [hmc] at h
    exact h
  -- step 3: (x₁, x₂, x₃) is still minimizing
  have hkey : ∀ t : M,
      workFnU E₀ τ ![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃]
          + workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
        ≤ workFnU E₀ τ ![Sum.inl t, Sum.inl x₂, Sum.inl x₃]
          + workFnU E₀ τ ![Sum.inr t, Sum.inl x₂, Sum.inl x₃] := by
    intro t
    obtain ⟨u₀, hu₀⟩ := (antipode_coord_eval M Δ hΔ0 hΔ C₀ σ t x₂ x₃).1
    rw [← hτ] at hu₀
    have hone := tree_one_server_potential_minimizer M hM v (2 * Δ) x₂ x₁
      (fun u => by
        have := hx₁ u
        have hc1 : dist x₂ x₁ = dist x₂ x₁ := rfl
        simpa [dist_comm x₂ x₁, dist_comm x₂ u] using this) t u₀
    have hb1 := hlipA x₁ u₀
    have hb2 := hlipA x₁ t
    rw [hres3 u₀ x₂ x₃] at hb1 hu₀
    rw [hres3 t x₂ x₃] at hb2 ⊢
    rw [hres3 x₁ x₂ x₃]
    rcases min_cases (v x₁ + v u₀ + 2 * Δ - dist x₁ u₀)
        (v x₁ + v t + 2 * Δ - dist x₁ t) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hone
    · have hc : dist u₀ x₁ = dist x₁ u₀ := dist_comm u₀ x₁
      have hc2 : dist u₀ t = dist t u₀ := dist_comm u₀ t
      rw [hu₀]
      show v x₁ + workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
          ≤ v t + (v u₀ + (2 * Δ - dist u₀ t))
      linarith
    · have hc : dist t x₁ = dist x₁ t := dist_comm t x₁
      have hc2 : dist u₀ t = dist t u₀ := dist_comm u₀ t
      rw [hu₀]
      show v x₁ + workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
          ≤ v t + (v u₀ + (2 * Δ - dist u₀ t))
      linarith
  have hmin : ∀ a b c : M,
      ckPotAt M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃ ≤ ckPotAt M Δ hΔ0 hΔ C₀ σ a b c := by
    intro a b c
    have h1 : ckPotAt M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃ ≤ ckPotAt M Δ hΔ0 hΔ C₀ σ y₁ x₂ x₃ := by
      rw [hΦ, hΦ]
      have := hkey y₁
      linarith
    exact le_trans h1 (hymin a b c)
  -- step 4: the resolution of (x̄₂, x̄₂, x₃) to x₁
  have hx₁' : ∀ u : M, workFnU C₀ σ ![x₃, x₁, x₂] - dist x₁ x₂
      ≤ workFnU C₀ σ ![x₃, u, x₂] - dist u x₂ := by
    intro u
    have h := hx₁ u
    have e1 : workFnU C₀ σ ![x₃, x₁, x₂] = v x₁ := by
      rw [hv]
      simp only
      exact (rot3 C₀ σ x₁ x₂ x₃).symm
    have e2 : workFnU C₀ σ ![x₃, u, x₂] = v u := by
      rw [hv]
      simp only
      exact (rot3 C₀ σ u x₂ x₃).symm
    rw [e1, e2]
    have hc1 : dist x₂ x₁ = dist x₁ x₂ := dist_comm x₂ x₁
    have hc2 : dist x₂ u = dist u x₂ := dist_comm x₂ u
    linarith
  obtain ⟨⟨p, q⟩, hpq⟩ := Finite.exists_min (fun t : M × M =>
    workFnU C₀ σ ![x₃, t.1, t.2] - dist t.1 x₂ - dist t.2 x₂)
  have hpq' : ∀ u w : M, workFnU C₀ σ ![x₃, p, q] - dist p x₂ - dist q x₂
      ≤ workFnU C₀ σ ![x₃, u, w] - dist u x₂ - dist w x₂ := fun u w => hpq ⟨u, w⟩
  obtain ⟨w', hw'⟩ := workFnU_dual_pair_exchange M C₀ σ x₂ x₃ x₁ p q hx₁' hpq'
  -- the two-antipode collapse
  obtain ⟨u₂, v₂, huv⟩ := (antipode_coord_eval M Δ hΔ0 hΔ C₀ σ x₂ x₂ x₃).2
  rw [← hτ] at huv
  have hlipB : ∀ a b : M,
      workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
        ≤ workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl x₃]
          + ((2 * Δ - dist a x₂) + (2 * Δ - dist b x₂)) := by
    intro a b
    have h := lip ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] ![Sum.inl a, Sum.inl b, Sum.inl x₃]
    have hmc : moveCost (![Sum.inl a, Sum.inl b, Sum.inl x₃] : Config 3 (M ⊕ M))
        ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
        = (2 * Δ - dist a x₂) + (2 * Δ - dist b x₂) := by
      rw [mc3]
      show (2 * Δ - dist a x₂) + (2 * Δ - dist b x₂) + dist x₃ x₃
          = (2 * Δ - dist a x₂) + (2 * Δ - dist b x₂)
      rw [dist_self]
      ring
    rw [hmc] at h
    exact h
  have hFconv : ∀ a b : M, workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl x₃]
      = workFnU C₀ σ ![x₃, a, b] := by
    intro a b
    rw [hres3 a b x₃]
    exact rot3 C₀ σ a b x₃
  -- (u₂, v₂) is a global minimizer of the dual pair functional
  have huvmin : ∀ a b : M,
      workFnU C₀ σ ![x₃, u₂, v₂] - dist u₂ x₂ - dist v₂ x₂
        ≤ workFnU C₀ σ ![x₃, a, b] - dist a x₂ - dist b x₂ := by
    intro a b
    have h1 := hlipB a b
    rw [hFconv a b] at h1
    rw [hFconv u₂ v₂] at huv
    linarith
  have hFeq : workFnU C₀ σ ![x₃, x₁, w'] - dist x₁ x₂ - dist w' x₂
      = workFnU C₀ σ ![x₃, u₂, v₂] - dist u₂ x₂ - dist v₂ x₂ :=
    le_antisymm (hw' u₂ v₂) (huvmin x₁ w')
  have hresolve : workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
      = workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃] + (2 * Δ - dist x₁ x₂) := by
    refine le_antisymm ?_ ?_
    · -- Lipschitz: move the first anchor to x̄₂
      have h := lip ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
      have hmc : moveCost (![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃] : Config 3 (M ⊕ M))
          ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] = 2 * Δ - dist x₁ x₂ := by
        rw [mc3]
        show dist x₂ x₂ + (2 * Δ - dist x₁ x₂) + dist x₃ x₃ = 2 * Δ - dist x₁ x₂
        rw [dist_self, dist_self]
        ring
      rw [hmc] at h
      exact h
    · -- the expansion through (x₁, w') collapses back
      have hcol : workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
          ≤ workFnU E₀ τ ![Sum.inl w', Sum.inl x₁, Sum.inl x₃] + (2 * Δ - dist w' x₂) := by
        have h := lip ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
          ![Sum.inl w', Sum.inl x₁, Sum.inl x₃]
        have hmc : moveCost (![Sum.inl w', Sum.inl x₁, Sum.inl x₃] : Config 3 (M ⊕ M))
            ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃] = 2 * Δ - dist w' x₂ := by
          rw [mc3]
          show (2 * Δ - dist w' x₂) + dist x₁ x₁ + dist x₃ x₃ = 2 * Δ - dist w' x₂
          rw [dist_self, dist_self]
          ring
        rw [hmc] at h
        exact h
      have hperm : workFnU E₀ τ ![Sum.inl w', Sum.inl x₁, Sum.inl x₃]
          = workFnU C₀ σ ![x₃, x₁, w'] := by
        rw [hres3 w' x₁ x₃]
        rw [rot3 C₀ σ w' x₁ x₃]
        exact swap12 C₀ σ x₃ w' x₁
      rw [hFconv u₂ v₂] at huv
      rw [hperm] at hcol
      linarith [hFeq, huv, hcol]
  refine ⟨?_, ?_, hresolve⟩
  · -- ckPot is attained at (x₁, x₂, x₃)
    refine le_antisymm (ckPot_le M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃) ?_
    rw [hy]
    exact hmin y₁ x₂ x₃
  · -- swap symmetry via the anchor-swap theorem
    have hbar : ∀ p q : M ⊕ M, dist (Sum.swap p) q = dist p (Sum.swap q) := by
      intro p q
      show antiD Δ (Sum.swap p) q = antiD Δ p (Sum.swap q)
      rw [antiD_swap_left, antiD_swap_right]
    have hswap := potential_anchor_swap (M ⊕ M) E₀ τ Sum.swap hbar
      (Sum.inl x₁) (Sum.inl x₂) (Sum.inl x₃) (by
        show workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
            = workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
              + dist (Sum.inl x₁ : M ⊕ M) (Sum.inr x₂)
        have hd : dist (Sum.inl x₁ : M ⊕ M) (Sum.inr x₂) = 2 * Δ - dist x₁ x₂ := rfl
        rw [hd]
        exact hresolve)
    refine le_antisymm ?_ ?_
    · rw [hΦ, hΦ]
      exact hswap
    · exact hmin x₂ x₁ x₃
