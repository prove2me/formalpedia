-- Prove2me | solution 1 for KServer.tree_anchor_at_request
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T07:41:40.448274+00:00
-- url     : https://prove2.me/submissions/884c6559-98e2-49c1-aa88-cb0408e62ba5

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential
import Definitions.Def_KServer_tree_metric
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_resolves
import Theorems.Thm_KServer_workFnU_quasiconvex_three
import Theorems.Thm_KServer_tree_swap_first_two
import Theorems.Thm_KServer_anchor_push_case
import Theorems.Thm_KServer_anchor_L26_case
import Theorems.Thm_KServer_anchor_quasiconvex_case

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
    (p q c : N) : workFnU C₀ σ ![p, q, c] = workFnU C₀ σ ![q, p, c] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 0 1) ?_
  intro i
  match i with
  | 0 => show p = ![q, p, c] ((Equiv.swap (0 : Fin 3) 1) 0); rw [Equiv.swap_apply_left]; rfl
  | 1 => show q = ![q, p, c] ((Equiv.swap (0 : Fin 3) 1) 1); rw [Equiv.swap_apply_right]; rfl
  | 2 => show c = ![q, p, c] ((Equiv.swap (0 : Fin 3) 1) 2)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl

/-- **The anchoring theorem**: on a tree, the Coester–Koutsoupias potential of a
sequence ending with the request `r` attains its minimum at an anchor triple whose
last anchor is `r`. -/
theorem solution (M : Type) [MetricSpace M] [Fintype M] [Nonempty M]
    (hM : IsTreeVertexSpace M) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ u v : M, dist u v ≤ Δ)
    (C₀ : Config 3 M) (σ : List M) (r : M) :
    ∃ y z : M, ckPot M Δ hΔ0 hΔ C₀ (σ ++ [r]) = ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) y z r := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := (σ ++ [r]).map Sum.inl with hτ
  have hτsplit : τ = σ.map Sum.inl ++ [Sum.inl r] := by rw [hτ]; simp
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have dLL : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inl b) = dist a b := fun _ _ => rfl
  have dLR : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inr b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  have hΦ : ∀ p q s : M, ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) p q s
      = workFnU E₀ τ ![Sum.inl p, Sum.inl q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr p, Sum.inl q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr q, Sum.inr q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr s, Sum.inr s, Sum.inr s] := fun p q s => rfl
  -- Lemma 25: a swap-symmetric minimizing triple with resolution to the first anchor
  obtain ⟨x₁, x₂, x₃, hm, hs, hr21⟩ := tree_swap_first_two M hM Δ hΔ0 hΔ C₀ (σ ++ [r])
  rw [← hτ] at hr21
  have hfin : ∀ y z : M,
      ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) y z r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₁ x₂ x₃ →
      ∃ y' z' : M, ckPot M Δ hΔ0 hΔ C₀ (σ ++ [r]) = ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) y' z' r := by
    intro y z h
    refine ⟨y, z, le_antisymm (ckPot_le M Δ hΔ0 hΔ C₀ (σ ++ [r]) y z r) ?_⟩
    rw [hm]
    exact h
  -- dispatch the resolution of the anchor triple itself
  obtain ⟨i, hi⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
    ![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃]
  rw [← hτsplit] at hi
  match i, hi with
  | ⟨0, _⟩, hi =>
    -- resolves from x₁: push case on (x₁, x₂, x₃)
    have hupd : Function.update (![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
        ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inl x₂, Sum.inl x₃] := by
      funext l
      match l with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    rw [hupd] at hi
    have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃] ⟨0, by norm_num⟩)
        = dist r x₁ := dLL r x₁
    rw [hd, dist_comm r x₁] at hi
    have hi' : workFnU E₀ τ ![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃]
        = workFnU E₀ τ ![Sum.inl r, Sum.inl x₂, Sum.inl x₃] + dist x₁ r := hi
    rcases anchor_push_case M Δ hΔ0 hΔ C₀ σ r x₁ x₂ x₃ (Or.inl hi') with h | h
    · exact hfin x₂ x₃ h
    · exact hfin x₃ x₂ h
  | ⟨1, _⟩, hi =>
    -- resolves from x₂: push case on the swapped triple (x₂, x₁, x₃)
    have hupd : Function.update (![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
        ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inl x₁, Sum.inl r, Sum.inl x₃] := by
      funext l
      match l with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    rw [hupd] at hi
    have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃] ⟨1, by norm_num⟩)
        = dist r x₂ := dLL r x₂
    rw [hd, dist_comm r x₂] at hi
    have hi' : workFnU E₀ τ ![Sum.inl x₂, Sum.inl x₁, Sum.inl x₃]
        = workFnU E₀ τ ![Sum.inl r, Sum.inl x₁, Sum.inl x₃] + dist x₂ r := by
      rw [swap01' E₀ τ (Sum.inl x₂) (Sum.inl x₁) (Sum.inl x₃), hi,
        ← swap01' E₀ τ (Sum.inl x₁) (Sum.inl r) (Sum.inl x₃)]
    rcases anchor_push_case M Δ hΔ0 hΔ C₀ σ r x₂ x₁ x₃ (Or.inl hi') with h | h
    · exact hfin x₁ x₃ (h.trans (le_of_eq hs))
    · exact hfin x₃ x₁ (h.trans (le_of_eq hs))
  | ⟨2, _⟩, hi =>
    -- resolves from x₃
    have hupd : Function.update (![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
        ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inl x₁, Sum.inl x₂, Sum.inl r] := by
      funext l
      match l with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    rw [hupd] at hi
    have hR3 : workFnU E₀ τ ![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃]
        = workFnU E₀ τ ![Sum.inl x₁, Sum.inl x₂, Sum.inl r] + dist r x₃ := hi
    -- dispatch the resolution of the antipodal companion (x̄₁, x₂, x₃)
    obtain ⟨i2, hi2⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
      ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
    rw [← hτsplit] at hi2
    match i2, hi2 with
    | ⟨0, _⟩, hi2 =>
      -- the antipodal server resolves: push case, antipodal branch
      have hupd2 : Function.update (![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
          ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inl x₂, Sum.inl x₃] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd2] at hi2
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃] ⟨0, by norm_num⟩)
          = 2 * Δ - dist r x₁ := dLR r x₁
      rw [hd, dist_comm r x₁] at hi2
      have hi' : workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
          = workFnU E₀ τ ![Sum.inl r, Sum.inl x₂, Sum.inl x₃] + (2 * Δ - dist x₁ r) := hi2
      rcases anchor_push_case M Δ hΔ0 hΔ C₀ σ r x₁ x₂ x₃ (Or.inr hi') with h | h
      · exact hfin x₂ x₃ h
      · exact hfin x₃ x₂ h
    | ⟨2, _⟩, hi2 =>
      -- both resolve in the third slot: the Lemma-26 case
      have hupd2 : Function.update (![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
          ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inr x₁, Sum.inl x₂, Sum.inl r] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd2] at hi2
      exact hfin x₁ x₂ (anchor_L26_case M hM Δ hΔ0 hΔ C₀ σ r x₁ x₂ x₃ hR3 hi2)
    | ⟨1, _⟩, hi2 =>
      -- the deep case: the companion resolves from the middle anchor
      have hupd2 : Function.update (![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
          ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inr x₁, Sum.inl r, Sum.inl x₃] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd2] at hi2
      have hR3b : workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
          = workFnU E₀ τ ![Sum.inr x₁, Sum.inl r, Sum.inl x₃] + dist r x₂ := hi2
      -- the swap symmetry forces r to lie between x₁ and x₂
      have hPQ : workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
            + workFnU E₀ τ ![Sum.inr x₁, Sum.inr x₁, Sum.inl x₃]
          = workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
            + workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] := by
        have h := hs
        rw [hΦ, hΦ] at h
        have hsw := swap01' E₀ τ (Sum.inl x₂) (Sum.inl x₁) (Sum.inl x₃)
        linarith
      have hlipA : workFnU E₀ τ ![Sum.inr x₁, Sum.inr x₁, Sum.inl x₃]
          ≤ workFnU E₀ τ ![Sum.inr x₁, Sum.inl r, Sum.inl x₃] + (2 * Δ - dist r x₁) := by
        have h := lip ![Sum.inr x₁, Sum.inr x₁, Sum.inl x₃] ![Sum.inr x₁, Sum.inl r, Sum.inl x₃]
        have hmc : moveCost (![Sum.inr x₁, Sum.inl r, Sum.inl x₃] : Config 3 (M ⊕ M))
            ![Sum.inr x₁, Sum.inr x₁, Sum.inl x₃] = 2 * Δ - dist r x₁ := by
          rw [mc3]
          show dist x₁ x₁ + dist (Sum.inl r : M ⊕ M) (Sum.inr x₁) + dist x₃ x₃
              = 2 * Δ - dist r x₁
          rw [dist_self, dist_self, dLR]
          ring
        rw [hmc] at h
        exact h
      have htri : dist x₁ x₂ ≤ dist x₁ r + dist r x₂ := dist_triangle x₁ r x₂
      have hcomm : dist x₁ r = dist r x₁ := dist_comm x₁ r
      have hs3 : dist x₁ x₂ = dist r x₁ + dist r x₂ := by linarith [hPQ, hr21, hR3b, hlipA]
      -- case on the from-antipode resolution equation for (x̄₂, x̄₂, x₃)
      by_cases hbb : workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
          = workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₃] + (2 * Δ - dist r x₂)
      · rcases anchor_quasiconvex_case M Δ hΔ0 hΔ C₀ σ r x₁ x₂ x₃ hR3 hR3b hbb with h | h
        · exact hfin x₂ x₃ h
        · exact hfin x₁ x₃ h
      · -- the doubled antipode must resolve from x₃
        obtain ⟨i3, hi3⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
          ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
        rw [← hτsplit] at hi3
        have ha2 : workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
            = workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl r] + dist r x₃ := by
          match i3, hi3 with
          | ⟨0, _⟩, hi3 =>
            exfalso
            have hupd3 : Function.update
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
                ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inr x₂, Sum.inl x₃] := by
              funext l
              match l with
              | 0 => rfl
              | 1 => rfl
              | 2 => rfl
            rw [hupd3] at hi3
            have hd : dist (Sum.inl r : M ⊕ M)
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] ⟨0, by norm_num⟩)
                = 2 * Δ - dist r x₂ := dLR r x₂
            rw [hd] at hi3
            refine hbb ?_
            rw [hi3, swap01' E₀ τ (Sum.inl r) (Sum.inr x₂) (Sum.inl x₃)]
          | ⟨1, _⟩, hi3 =>
            exfalso
            have hupd3 : Function.update
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
                ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inr x₂, Sum.inl r, Sum.inl x₃] := by
              funext l
              match l with
              | 0 => rfl
              | 1 => rfl
              | 2 => rfl
            rw [hupd3] at hi3
            exact hbb hi3
          | ⟨2, _⟩, hi3 =>
            have hupd3 : Function.update
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] : Config 3 (M ⊕ M))
                ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inr x₂, Sum.inr x₂, Sum.inl r] := by
              funext l
              match l with
              | 0 => rfl
              | 1 => rfl
              | 2 => rfl
            rw [hupd3] at hi3
            exact hi3
        -- the second quasiconvex pairing
        have qc2 := workFnU_quasiconvex_three (M ⊕ M) E₀ τ (Sum.inr x₂) (Sum.inr x₂)
          (Sum.inl r) (Sum.inl x₁) (Sum.inl x₃)
        -- Lipschitz halves used to convert forced inequalities into resolutions
        have hL1 : workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
            ≤ workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl r] + dist r x₃ := by
          have h := lip ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃] ![Sum.inr x₂, Sum.inl x₁, Sum.inl r]
          have hmc : moveCost (![Sum.inr x₂, Sum.inl x₁, Sum.inl r] : Config 3 (M ⊕ M))
              ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃] = dist r x₃ := by
            rw [mc3]
            show dist x₂ x₂ + dist x₁ x₁ + dist r x₃ = dist r x₃
            rw [dist_self, dist_self]
            ring
          rw [hmc] at h
          exact h
        have hswap121 : workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₁]
            = workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl r] :=
          swap12 E₀ τ (Sum.inr x₂) (Sum.inl r) (Sum.inl x₁)
        have hfinish_L26 : workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
              = workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl r] + dist r x₃ →
            ∃ y' z' : M, ckPot M Δ hΔ0 hΔ C₀ (σ ++ [r])
              = ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) y' z' r := by
          intro hs1
          have h0' : workFnU E₀ τ ![Sum.inl x₂, Sum.inl x₁, Sum.inl x₃]
              = workFnU E₀ τ ![Sum.inl x₂, Sum.inl x₁, Sum.inl r] + dist r x₃ := by
            rw [swap01' E₀ τ (Sum.inl x₂) (Sum.inl x₁) (Sum.inl x₃), hR3,
              ← swap01' E₀ τ (Sum.inl x₁) (Sum.inl x₂) (Sum.inl r)]
          exact hfin x₂ x₁
            ((anchor_L26_case M hM Δ hΔ0 hΔ C₀ σ r x₂ x₁ x₃ h0' hs1).trans (le_of_eq hs))
        rcases min_cases
            (workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₁]
              + workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₃])
            (workFnU E₀ τ ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
              + workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₁]) with ⟨he, -⟩ | ⟨he, -⟩ <;>
          rw [he] at qc2
        · -- pairing (x̄₂, x₁) with (r, x₃): dispatch the resolution of (x̄₂, x̄₂, x₁)
          obtain ⟨j, hj⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
            ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₁]
          rw [← hτsplit] at hj
          match j, hj with
          | ⟨0, _⟩, hj =>
            have hupd4 : Function.update
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₁] : Config 3 (M ⊕ M))
                ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inr x₂, Sum.inl x₁] := by
              funext l
              match l with
              | 0 => rfl
              | 1 => rfl
              | 2 => rfl
            rw [hupd4, swap01' E₀ τ (Sum.inl r) (Sum.inr x₂) (Sum.inl x₁)] at hj
            have hd : dist (Sum.inl r : M ⊕ M)
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₁] ⟨0, by norm_num⟩)
                = 2 * Δ - dist r x₂ := dLR r x₂
            rw [hd] at hj
            -- forced equalities give the resolution of (x̄₂, x₁, x₃) from x₃
            have hL2 : workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
                ≤ workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₃] + dist r x₁ := by
              have h := lip ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
                ![Sum.inr x₂, Sum.inl r, Sum.inl x₃]
              have hmc : moveCost (![Sum.inr x₂, Sum.inl r, Sum.inl x₃] : Config 3 (M ⊕ M))
                  ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃] = dist r x₁ := by
                rw [mc3]
                show dist x₂ x₂ + dist r x₁ + dist x₃ x₃ = dist r x₁
                rw [dist_self, dist_self]
                ring
              rw [hmc] at h
              exact h
            refine hfinish_L26 (le_antisymm hL1 ?_)
            linarith [qc2, hj, ha2, hr21, hs3, hL1, hL2, hswap121]
          | ⟨1, _⟩, hj =>
            have hupd4 : Function.update
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₁] : Config 3 (M ⊕ M))
                ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inr x₂, Sum.inl r, Sum.inl x₁] := by
              funext l
              match l with
              | 0 => rfl
              | 1 => rfl
              | 2 => rfl
            rw [hupd4] at hj
            have hd : dist (Sum.inl r : M ⊕ M)
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₁] ⟨1, by norm_num⟩)
                = 2 * Δ - dist r x₂ := dLR r x₂
            rw [hd] at hj
            have hL2 : workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
                ≤ workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₃] + dist r x₁ := by
              have h := lip ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃]
                ![Sum.inr x₂, Sum.inl r, Sum.inl x₃]
              have hmc : moveCost (![Sum.inr x₂, Sum.inl r, Sum.inl x₃] : Config 3 (M ⊕ M))
                  ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃] = dist r x₁ := by
                rw [mc3]
                show dist x₂ x₂ + dist r x₁ + dist x₃ x₃ = dist r x₁
                rw [dist_self, dist_self]
                ring
              rw [hmc] at h
              exact h
            refine hfinish_L26 (le_antisymm hL1 ?_)
            linarith [qc2, hj, ha2, hr21, hs3, hL1, hL2, hswap121]
          | ⟨2, _⟩, hj =>
            -- resolution from x₁ contradicts ¬hbb
            exfalso
            have hupd4 : Function.update
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₁] : Config 3 (M ⊕ M))
                ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inr x₂, Sum.inr x₂, Sum.inl r] := by
              funext l
              match l with
              | 0 => rfl
              | 1 => rfl
              | 2 => rfl
            rw [hupd4] at hj
            have hd : dist (Sum.inl r : M ⊕ M)
                (![Sum.inr x₂, Sum.inr x₂, Sum.inl x₁] ⟨2, by norm_num⟩)
                = dist r x₁ := dLL r x₁
            rw [hd] at hj
            have hγ : workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₃] + dist r x₁
                ≤ workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₁, Sum.inl x₃] := by
              linarith [qc2, hj, ha2]
            refine hbb (le_antisymm ?_ ?_)
            · have h := lip ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
                ![Sum.inr x₂, Sum.inl r, Sum.inl x₃]
              have hmc : moveCost (![Sum.inr x₂, Sum.inl r, Sum.inl x₃] : Config 3 (M ⊕ M))
                  ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃] = 2 * Δ - dist r x₂ := by
                rw [mc3]
                show dist x₂ x₂ + dist (Sum.inl r : M ⊕ M) (Sum.inr x₂) + dist x₃ x₃
                    = 2 * Δ - dist r x₂
                rw [dist_self, dist_self, dLR]
                ring
              rw [hmc] at h
              exact h
            · linarith [hr21, hγ, hs3]
        · -- pairing (x̄₂, x₃) with (r, x₁): the resolution of (x̄₂, x₁, x₃) from x₃ is direct
          refine hfinish_L26 (le_antisymm hL1 ?_)
          linarith [qc2, ha2, hr21, hswap121]
