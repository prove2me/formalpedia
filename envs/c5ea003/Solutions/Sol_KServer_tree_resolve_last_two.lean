-- Prove2me | solution 1 for KServer.tree_resolve_last_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T06:21:30.970424+00:00
-- url     : https://prove2.me/submissions/4753b5f6-a45b-47d2-bcc1-93a67d585405

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_tree_metric
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_resolves
import Theorems.Thm_KServer_workFnU_mcshane_request
import Theorems.Thm_KServer_workFnU_antipodal_extension_restrict
import Theorems.Thm_KServer_tree_four_point

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

/-- **Coester–Koutsoupias, Lemma 26, for three servers.** -/
theorem solution (M : Type) [MetricSpace M] [Fintype M] (hM : IsTreeVertexSpace M)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ u v : M, dist u v ≤ Δ)
    (C₀ : Config 3 M) (σ : List M) (r x y : M) :
    @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x, Sum.inr x, Sum.inl r]
      + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inr r]
    ≤ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x, Sum.inr x, Sum.inl y]
      + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inr y, Sum.inr y]
      + 2 * dist r y := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := (σ ++ [r]).map Sum.inl with hτ
  have hτsplit : τ = σ.map Sum.inl ++ [Sum.inl r] := by rw [hτ]; simp
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  -- distance tables
  have dLL : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inl b) = dist a b := fun _ _ => rfl
  have dRR : ∀ a b : M, dist (Sum.inr a : M ⊕ M) (Sum.inr b) = dist a b := fun _ _ => rfl
  have dLR : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inr b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  have dRL : ∀ a b : M, dist (Sum.inr a : M ⊕ M) (Sum.inl b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  -- Lipschitz in the extension, specialised
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  -- resolve the configuration (x̄, x̄, y)
  obtain ⟨i, hi⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
    ![Sum.inr x, Sum.inr x, Sum.inl y]
  rw [← hτsplit] at hi
  -- case split on which server resolves
  have hxxy : (workFnU E₀ τ ![Sum.inr x, Sum.inr x, Sum.inl y]
        = workFnU E₀ τ ![Sum.inr x, Sum.inr x, Sum.inl r] + dist r y)
      ∨ (workFnU E₀ τ ![Sum.inr x, Sum.inr x, Sum.inl y]
        = workFnU E₀ τ ![Sum.inr x, Sum.inl y, Sum.inl r] + (2 * Δ - dist r x)) := by
    match i, hi with
    | ⟨0, _⟩, hi =>
      right
      have hupd : Function.update (![Sum.inr x, Sum.inr x, Sum.inl y] : Config 3 (M ⊕ M))
          ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inr x, Sum.inl y] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hperm : workFnU E₀ τ ![Sum.inl r, Sum.inr x, Sum.inl y]
          = workFnU E₀ τ ![Sum.inr x, Sum.inl y, Sum.inl r] :=
        (rot3 E₀ τ (Sum.inr x) (Sum.inl y) (Sum.inl r)).symm
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr x, Sum.inr x, Sum.inl y] ⟨0, by norm_num⟩)
          = 2 * Δ - dist r x := dLR r x
      rw [hperm, hd] at hi
      exact hi
    | ⟨1, _⟩, hi =>
      right
      have hupd : Function.update (![Sum.inr x, Sum.inr x, Sum.inl y] : Config 3 (M ⊕ M))
          ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inr x, Sum.inl r, Sum.inl y] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hperm : workFnU E₀ τ ![Sum.inr x, Sum.inl r, Sum.inl y]
          = workFnU E₀ τ ![Sum.inr x, Sum.inl y, Sum.inl r] :=
        swap12 E₀ τ (Sum.inr x) (Sum.inl r) (Sum.inl y)
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr x, Sum.inr x, Sum.inl y] ⟨1, by norm_num⟩)
          = 2 * Δ - dist r x := dLR r x
      rw [hperm, hd] at hi
      exact hi
    | ⟨2, _⟩, hi =>
      left
      have hupd : Function.update (![Sum.inr x, Sum.inr x, Sum.inl y] : Config 3 (M ⊕ M))
          ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inr x, Sum.inr x, Sum.inl r] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr x, Sum.inr x, Sum.inl y] ⟨2, by norm_num⟩)
          = dist r y := dLL r y
      rw [hd] at hi
      exact hi
  rcases hxxy with hres | hres
  · -- Case 1: the y-server resolves; Lipschitz from ȳ³ to r̄³
    have hlip := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inr y, Sum.inr y, Sum.inr y]
    have hmc : moveCost (![Sum.inr y, Sum.inr y, Sum.inr y] : Config 3 (M ⊕ M))
        ![Sum.inr r, Sum.inr r, Sum.inr r] = 3 * dist y r := by
      rw [mc3]
      show dist (Sum.inr y : M ⊕ M) (Sum.inr r) + dist (Sum.inr y : M ⊕ M) (Sum.inr r)
          + dist (Sum.inr y : M ⊕ M) (Sum.inr r) = 3 * dist y r
      rw [dRR]
      ring
    rw [hmc] at hlip
    have hcomm : dist y r = dist r y := dist_comm y r
    rw [hres]
    linarith
  · -- Case 2: an x̄-server resolves
    -- expand ȳ³ through an original configuration containing r
    obtain ⟨A, ⟨j, hAj⟩, hA⟩ := workFnU_mcshane_request 3 h3 M Δ hΔ0 hΔ C₀ σ r
      ![Sum.inr y, Sum.inr y, Sum.inr y]
    rw [← hτ] at hA
    -- normalise A to the form ![a, b, r]
    have hAeta : A = ![A 0, A 1, A 2] := by
      funext l
      match l with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    -- the two non-request coordinates
    obtain ⟨a, b, hab⟩ : ∃ a b : M, workFnU C₀ (σ ++ [r]) A = workFnU C₀ (σ ++ [r]) ![a, b, r]
        ∧ dist (A 0) y + dist (A 1) y + dist (A 2) y = dist a y + dist b y + dist r y := by
      match j, hAj with
      | ⟨0, _⟩, hAj =>
        refine ⟨A 1, A 2, ?_, ?_⟩
        · conv_lhs => rw [hAeta]
          have h0 : A 0 = r := hAj
          rw [h0]
          exact (rot3 C₀ (σ ++ [r]) (A 1) (A 2) r).symm ▸ rot3 C₀ (σ ++ [r]) (A 1) (A 2) r
        · have h0 : A 0 = r := hAj
          rw [h0]
          ring
      | ⟨1, _⟩, hAj =>
        refine ⟨A 0, A 2, ?_, ?_⟩
        · conv_lhs => rw [hAeta]
          have h1 : A 1 = r := hAj
          rw [h1]
          exact swap12 C₀ (σ ++ [r]) (A 0) r (A 2)
        · have h1 : A 1 = r := hAj
          rw [h1]
          ring
      | ⟨2, _⟩, hAj =>
        refine ⟨A 0, A 1, ?_, ?_⟩
        · conv_lhs => rw [hAeta]
          have h2 : A 2 = r := hAj
          rw [h2]
        · have h2 : A 2 = r := hAj
          rw [h2]
    -- the matching cost from the embedded A to ȳ³
    have hmcA : @moveCost 3 (M ⊕ M) _ (fun i => Sum.inl (A i))
        ![Sum.inr y, Sum.inr y, Sum.inr y]
        = 6 * Δ - (dist (A 0) y + dist (A 1) y + dist (A 2) y) := by
      rw [mc3]
      show dist (Sum.inl (A 0) : M ⊕ M) (Sum.inr y) + dist (Sum.inl (A 1) : M ⊕ M) (Sum.inr y)
          + dist (Sum.inl (A 2) : M ⊕ M) (Sum.inr y)
          = 6 * Δ - (dist (A 0) y + dist (A 1) y + dist (A 2) y)
      rw [dLR, dLR, dLR]
      ring
    -- pass to the extension value of ![a,b,r]
    have hemb : (fun i => Sum.inl ((![a, b, r] : Config 3 M) i) : Config 3 (M ⊕ M))
        = ![Sum.inl a, Sum.inl b, Sum.inl r] := by
      funext l
      match l with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    have hrestr := workFnU_antipodal_extension_restrict 3 h3 M Δ hΔ0 hΔ C₀ (σ ++ [r]) ![a, b, r]
    rw [hemb] at hrestr
    rw [← hτ] at hrestr
    -- the assembled expansion of ȳ³
    have hyyy : workFnU E₀ τ ![Sum.inr y, Sum.inr y, Sum.inr y]
        = workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl r]
          + (6 * Δ - (dist a y + dist b y + dist r y)) := by
      rw [hA, hmcA, hab.1, hab.2, ← hrestr]
    -- case split on the quasiconcavity dichotomy
    by_cases h2a : dist r x + dist a y ≤ dist x y + dist a r
    · -- sub-case 2a with the anchor a
      have hby : workFnU E₀ τ ![Sum.inl a, Sum.inr y, Sum.inr y]
          ≤ workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl r] + ((2 * Δ - dist b y) + (2 * Δ - dist r y)) := by
        have h := lip ![Sum.inl a, Sum.inr y, Sum.inr y] ![Sum.inl a, Sum.inl b, Sum.inl r]
        have hmc : moveCost (![Sum.inl a, Sum.inl b, Sum.inl r] : Config 3 (M ⊕ M))
            ![Sum.inl a, Sum.inr y, Sum.inr y]
            = (2 * Δ - dist b y) + (2 * Δ - dist r y) := by
          rw [mc3]
          show dist (Sum.inl a : M ⊕ M) (Sum.inl a) + dist (Sum.inl b : M ⊕ M) (Sum.inr y)
              + dist (Sum.inl r : M ⊕ M) (Sum.inr y)
              = (2 * Δ - dist b y) + (2 * Δ - dist r y)
          rw [dLL, dLR, dLR, dist_self]
          ring
        rw [hmc] at h
        exact h
      have hrr : workFnU E₀ τ ![Sum.inl a, Sum.inr r, Sum.inr r]
          ≤ workFnU E₀ τ ![Sum.inl a, Sum.inr y, Sum.inr y] + 2 * dist y r := by
        have h := lip ![Sum.inl a, Sum.inr r, Sum.inr r] ![Sum.inl a, Sum.inr y, Sum.inr y]
        have hmc : moveCost (![Sum.inl a, Sum.inr y, Sum.inr y] : Config 3 (M ⊕ M))
            ![Sum.inl a, Sum.inr r, Sum.inr r] = 2 * dist y r := by
          rw [mc3]
          show dist (Sum.inl a : M ⊕ M) (Sum.inl a) + dist (Sum.inr y : M ⊕ M) (Sum.inr r)
              + dist (Sum.inr y : M ⊕ M) (Sum.inr r) = 2 * dist y r
          rw [dLL, dRR, dist_self]
          ring
        rw [hmc] at h
        exact h
      have hxx : workFnU E₀ τ ![Sum.inr x, Sum.inr x, Sum.inl r]
          ≤ workFnU E₀ τ ![Sum.inr x, Sum.inl y, Sum.inl r] + (2 * Δ - dist y x) := by
        have h := lip ![Sum.inr x, Sum.inr x, Sum.inl r] ![Sum.inr x, Sum.inl y, Sum.inl r]
        have hmc : moveCost (![Sum.inr x, Sum.inl y, Sum.inl r] : Config 3 (M ⊕ M))
            ![Sum.inr x, Sum.inr x, Sum.inl r] = 2 * Δ - dist y x := by
          rw [mc3]
          show dist (Sum.inr x : M ⊕ M) (Sum.inr x) + dist (Sum.inl y : M ⊕ M) (Sum.inr x)
              + dist (Sum.inl r : M ⊕ M) (Sum.inl r) = 2 * Δ - dist y x
          rw [dRR, dLR, dLL, dist_self, dist_self]
          ring
        rw [hmc] at h
        exact h
      have hr3 : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
          ≤ workFnU E₀ τ ![Sum.inl a, Sum.inr r, Sum.inr r] + (2 * Δ - dist a r) := by
        have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inl a, Sum.inr r, Sum.inr r]
        have hmc : moveCost (![Sum.inl a, Sum.inr r, Sum.inr r] : Config 3 (M ⊕ M))
            ![Sum.inr r, Sum.inr r, Sum.inr r] = 2 * Δ - dist a r := by
          rw [mc3]
          show dist (Sum.inl a : M ⊕ M) (Sum.inr r) + dist (Sum.inr r : M ⊕ M) (Sum.inr r)
              + dist (Sum.inr r : M ⊕ M) (Sum.inr r) = 2 * Δ - dist a r
          rw [dLR, dRR, dist_self]
          ring
        rw [hmc] at h
        exact h
      have hc1 : dist y r = dist r y := dist_comm y r
      have hc2 : dist y x = dist x y := dist_comm y x
      rw [hres, hyyy]
      linarith
    · push_neg at h2a
      by_cases h2b : dist r x + dist b y ≤ dist x y + dist b r
      · -- sub-case 2a with the anchor b
        have hby : workFnU E₀ τ ![Sum.inr y, Sum.inl b, Sum.inr y]
            ≤ workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl r]
              + ((2 * Δ - dist a y) + (2 * Δ - dist r y)) := by
          have h := lip ![Sum.inr y, Sum.inl b, Sum.inr y] ![Sum.inl a, Sum.inl b, Sum.inl r]
          have hmc : moveCost (![Sum.inl a, Sum.inl b, Sum.inl r] : Config 3 (M ⊕ M))
              ![Sum.inr y, Sum.inl b, Sum.inr y]
              = (2 * Δ - dist a y) + (2 * Δ - dist r y) := by
            rw [mc3]
            show dist (Sum.inl a : M ⊕ M) (Sum.inr y) + dist (Sum.inl b : M ⊕ M) (Sum.inl b)
                + dist (Sum.inl r : M ⊕ M) (Sum.inr y)
                = (2 * Δ - dist a y) + (2 * Δ - dist r y)
            rw [dLR, dLL, dLR, dist_self]
            ring
          rw [hmc] at h
          exact h
        have hrr : workFnU E₀ τ ![Sum.inr r, Sum.inl b, Sum.inr r]
            ≤ workFnU E₀ τ ![Sum.inr y, Sum.inl b, Sum.inr y] + 2 * dist y r := by
          have h := lip ![Sum.inr r, Sum.inl b, Sum.inr r] ![Sum.inr y, Sum.inl b, Sum.inr y]
          have hmc : moveCost (![Sum.inr y, Sum.inl b, Sum.inr y] : Config 3 (M ⊕ M))
              ![Sum.inr r, Sum.inl b, Sum.inr r] = 2 * dist y r := by
            rw [mc3]
            show dist (Sum.inr y : M ⊕ M) (Sum.inr r) + dist (Sum.inl b : M ⊕ M) (Sum.inl b)
                + dist (Sum.inr y : M ⊕ M) (Sum.inr r) = 2 * dist y r
            rw [dRR, dLL, dist_self]
            ring
          rw [hmc] at h
          exact h
        have hxx : workFnU E₀ τ ![Sum.inr x, Sum.inr x, Sum.inl r]
            ≤ workFnU E₀ τ ![Sum.inr x, Sum.inl y, Sum.inl r] + (2 * Δ - dist y x) := by
          have h := lip ![Sum.inr x, Sum.inr x, Sum.inl r] ![Sum.inr x, Sum.inl y, Sum.inl r]
          have hmc : moveCost (![Sum.inr x, Sum.inl y, Sum.inl r] : Config 3 (M ⊕ M))
              ![Sum.inr x, Sum.inr x, Sum.inl r] = 2 * Δ - dist y x := by
            rw [mc3]
            show dist (Sum.inr x : M ⊕ M) (Sum.inr x) + dist (Sum.inl y : M ⊕ M) (Sum.inr x)
                + dist (Sum.inl r : M ⊕ M) (Sum.inl r) = 2 * Δ - dist y x
            rw [dRR, dLR, dLL, dist_self, dist_self]
            ring
          rw [hmc] at h
          exact h
        have hr3 : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
            ≤ workFnU E₀ τ ![Sum.inr r, Sum.inl b, Sum.inr r] + (2 * Δ - dist b r) := by
          have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inr r, Sum.inl b, Sum.inr r]
          have hmc : moveCost (![Sum.inr r, Sum.inl b, Sum.inr r] : Config 3 (M ⊕ M))
              ![Sum.inr r, Sum.inr r, Sum.inr r] = 2 * Δ - dist b r := by
            rw [mc3]
            show dist (Sum.inr r : M ⊕ M) (Sum.inr r) + dist (Sum.inl b : M ⊕ M) (Sum.inr r)
                + dist (Sum.inr r : M ⊕ M) (Sum.inr r) = 2 * Δ - dist b r
            rw [dRR, dLR, dist_self]
            ring
          rw [hmc] at h
          exact h
        have hc1 : dist y r = dist r y := dist_comm y r
        have hc2 : dist y x = dist x y := dist_comm y x
        rw [hres, hyyy]
        linarith
      · -- sub-case 2b: quasiconcavity forces the exchanged equalities
        push_neg at h2b
        have heqa : dist r x + dist a y = dist r y + dist a x := by
          have h4a := tree_four_point M hM r x a y
          have h4b := tree_four_point M hM r y a x
          have hca : dist x a = dist a x := dist_comm x a
          have hcb : dist y a = dist a y := dist_comm y a
          have hcx : dist x y = dist y x := dist_comm x y
          have har : dist a r = dist r a := dist_comm a r
          rcases max_cases (dist r a + dist x y) (dist r y + dist x a) with ⟨he, -⟩ | ⟨he, -⟩ <;>
            rcases max_cases (dist r a + dist y x) (dist r x + dist y a) with ⟨he2, -⟩ | ⟨he2, -⟩ <;>
            rw [he] at h4a <;> rw [he2] at h4b <;>
            first
            | (exfalso
               linarith)
            | linarith
        have heqb : dist r x + dist b y = dist r y + dist b x := by
          have h4a := tree_four_point M hM r x b y
          have h4b := tree_four_point M hM r y b x
          have hca : dist x b = dist b x := dist_comm x b
          have hcb : dist y b = dist b y := dist_comm y b
          have hcx : dist x y = dist y x := dist_comm x y
          have har : dist b r = dist r b := dist_comm b r
          rcases max_cases (dist r b + dist x y) (dist r y + dist x b) with ⟨he, -⟩ | ⟨he, -⟩ <;>
            rcases max_cases (dist r b + dist y x) (dist r x + dist y b) with ⟨he2, -⟩ | ⟨he2, -⟩ <;>
            rw [he] at h4a <;> rw [he2] at h4b <;>
            first
            | (exfalso
               linarith)
            | linarith
        have hr3 : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
            ≤ workFnU E₀ τ ![Sum.inr x, Sum.inl y, Sum.inl r]
              + (dist x r + (2 * Δ - dist y r) + 2 * Δ) := by
          have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inr x, Sum.inl y, Sum.inl r]
          have hmc : moveCost (![Sum.inr x, Sum.inl y, Sum.inl r] : Config 3 (M ⊕ M))
              ![Sum.inr r, Sum.inr r, Sum.inr r]
              = dist x r + (2 * Δ - dist y r) + 2 * Δ := by
            rw [mc3]
            show dist (Sum.inr x : M ⊕ M) (Sum.inr r) + dist (Sum.inl y : M ⊕ M) (Sum.inr r)
                + dist (Sum.inl r : M ⊕ M) (Sum.inr r)
                = dist x r + (2 * Δ - dist y r) + 2 * Δ
            rw [dRR, dLR, dLR, dist_self]
            ring
          rw [hmc] at h
          exact h
        have hx2 : workFnU E₀ τ ![Sum.inr x, Sum.inr x, Sum.inl r]
            ≤ workFnU E₀ τ ![Sum.inl a, Sum.inl b, Sum.inl r]
              + ((2 * Δ - dist a x) + (2 * Δ - dist b x)) := by
          have h := lip ![Sum.inr x, Sum.inr x, Sum.inl r] ![Sum.inl a, Sum.inl b, Sum.inl r]
          have hmc : moveCost (![Sum.inl a, Sum.inl b, Sum.inl r] : Config 3 (M ⊕ M))
              ![Sum.inr x, Sum.inr x, Sum.inl r]
              = (2 * Δ - dist a x) + (2 * Δ - dist b x) := by
            rw [mc3]
            show dist (Sum.inl a : M ⊕ M) (Sum.inr x) + dist (Sum.inl b : M ⊕ M) (Sum.inr x)
                + dist (Sum.inl r : M ⊕ M) (Sum.inl r)
                = (2 * Δ - dist a x) + (2 * Δ - dist b x)
            rw [dLR, dLR, dLL, dist_self]
            ring
          rw [hmc] at h
          exact h
        have hcxr : dist x r = dist r x := dist_comm x r
        have hcyr : dist y r = dist r y := dist_comm y r
        rw [hres, hyyy]
        linarith
