-- Prove2me | solution 1 for KServer.workFnU_mcshane_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T05:55:04.85645+00:00
-- url     : https://prove2.me/submissions/001960b8-5100-41de-b575-dbe5b5b64376

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_antipodal_extension_restrict

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k))) = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem update_comp {k : ℕ} {M : Type} (X : Config k M) (i : Fin k) (r : M)
    (π : Equiv.Perm (Fin k)) :
    (Function.update X i r) ∘ (π : Equiv.Perm (Fin k))
      = Function.update (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) r := by
  classical
  funext l
  by_cases h : l = π.symm i
  · subst h
    rw [Function.comp_apply, Equiv.apply_symm_apply, Function.update_self,
      Function.update_self]
  · have h2 : (π : Equiv.Perm (Fin k)) l ≠ i := by
      intro hc; exact h (by rw [← hc]; simp)
    simp [Function.update_of_ne h, Function.update_of_ne h2]

private theorem wfU_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  obtain ⟨i', hi'⟩ := workFn_rec_ge k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k)))
  refine ⟨π i', ?_⟩
  have hup : Function.update (X ∘ (π : Equiv.Perm (Fin k))) i' r
      = (Function.update X (π i') r) ∘ (π : Equiv.Perm (Fin k)) := by
    rw [update_comp X (π i') r π]; simp
  rw [hup] at hi'
  have h1 := wfU_le C₀ σ (Function.update X (π i') r) π
  have h2 : (X ∘ (π : Equiv.Perm (Fin k))) i' = X (π i') := rfl
  rw [h2, hπ] at hi'
  linarith

private theorem wfU_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  refine workFn_covered k hk M C₀ σ r (X ∘ π) ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

private theorem mc_upd {k : ℕ} {N : Type} [MetricSpace N] (Z : Config k N) (i : Fin k)
    (p : N) : moveCost (Function.update Z i p) Z = dist p (Z i) := by
  unfold moveCost
  rw [Finset.sum_eq_single i]
  · rw [Function.update_self]
  · intro j _ hj
    rw [Function.update_of_ne hj, dist_self]
  · intro h
    exact absurd (Finset.mem_univ i) h

section Ext

variable (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
  (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)

include hk

/-- The Lipschitz upper bound, valid for every original configuration. -/
private theorem mcshane_le (C₀ : Config k M) (σ : List M) (Z : Config k (M ⊕ M))
    (X : Config k M) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) Z
      ≤ workFnU C₀ σ X
        + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (X i)) Z := by
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  have h1 := workFnU_lipschitz k hk (M ⊕ M) (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl)
    Z (fun i => Sum.inl (X i))
  have h2 := workFnU_antipodal_extension_restrict k hk M Δ hΔ0 hΔ C₀ σ X
  linarith

/-- The reverse inequality, by induction along the request sequence. -/
private theorem mcshane_ge (C₀ : Config k M) (σ : List M) (Z : Config k (M ⊕ M)) :
    ∃ X : Config k M,
      workFnU C₀ σ X
        + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (X i)) Z
      ≤ @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) Z := by
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  induction σ using List.reverseRecOn generalizing Z with
  | nil =>
    obtain ⟨π₀, hπ₀⟩ := wfU_exists (fun i => Sum.inl (C₀ i) : Config k (M ⊕ M)) [] Z
    refine ⟨C₀ ∘ (π₀⁻¹ : Equiv.Perm (Fin k)), ?_⟩
    have hX0 : workFnU C₀ [] (C₀ ∘ (π₀⁻¹ : Equiv.Perm (Fin k))) ≤ 0 := by
      have h := wfU_le C₀ [] (C₀ ∘ (π₀⁻¹ : Equiv.Perm (Fin k))) π₀
      rw [workFn_nil k hk M C₀ ((C₀ ∘ (π₀⁻¹ : Equiv.Perm (Fin k))) ∘ (π₀ : Equiv.Perm (Fin k)))]
        at h
      have he : ((C₀ ∘ (π₀⁻¹ : Equiv.Perm (Fin k))) ∘ (π₀ : Equiv.Perm (Fin k))) = C₀ := by
        funext i
        simp
      rw [he] at h
      have h0 : moveCost C₀ C₀ = 0 := by
        unfold moveCost
        simp
      rw [h0] at h
      exact h
    have hmc : @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl ((C₀ ∘ (π₀⁻¹ : Equiv.Perm (Fin k))) i)) Z
        = @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
            (fun i => Sum.inl (C₀ i)) ([] : List (M ⊕ M)) Z := by
      rw [← hπ₀]
      rw [workFn_nil k hk (M ⊕ M) (fun i => Sum.inl (C₀ i))
        (Z ∘ (π₀ : Equiv.Perm (Fin k)))]
      have := mc_perm (fun i => Sum.inl ((C₀ ∘ (π₀⁻¹ : Equiv.Perm (Fin k))) i) : Config k (M ⊕ M)) Z π₀
      rw [← this]
      have he : ((fun i => Sum.inl ((C₀ ∘ (π₀⁻¹ : Equiv.Perm (Fin k))) i) : Config k (M ⊕ M))
          ∘ (π₀ : Equiv.Perm (Fin k))) = fun i => Sum.inl (C₀ i) := by
        funext i
        simp
      rw [he]
    have hmap : (([] : List M).map (Sum.inl : M → M ⊕ M)) = ([] : List (M ⊕ M)) := rfl
    rw [hmap, hmc]
    linarith
  | append_singleton σ' r ih =>
    have hmap : ((σ' ++ [r]).map (Sum.inl : M → M ⊕ M))
        = σ'.map Sum.inl ++ [Sum.inl r] := by simp
    obtain ⟨i, hi⟩ := wfU_rec_ge k hk (M ⊕ M) (fun i => Sum.inl (C₀ i)) (σ'.map Sum.inl)
      (Sum.inl r) Z
    set Y₀ : Config k (M ⊕ M) := Function.update Z i (Sum.inl r) with hY₀
    obtain ⟨X, hX⟩ := ih Y₀
    -- the surgery configuration: replace antipodal coordinates of Y₀ by X's
    set W : Config k M := fun j => Sum.elim id (fun _ => X j) (Y₀ j) with hW
    have hWr : W i = r := by
      rw [hW]
      simp only [hY₀, Function.update_self]
      rfl
    have hsurg : moveCost (fun j => Sum.inl (X j) : Config k (M ⊕ M)) (fun j => Sum.inl (W j))
          + moveCost (fun j => Sum.inl (W j) : Config k (M ⊕ M)) Z
        ≤ moveCost (fun j => Sum.inl (X j) : Config k (M ⊕ M)) Y₀
          + moveCost Y₀ Z := by
      unfold moveCost
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      show dist (Sum.inl (X j) : M ⊕ M) (Sum.inl (W j)) + dist (Sum.inl (W j) : M ⊕ M) (Z j)
        ≤ dist (Sum.inl (X j) : M ⊕ M) (Y₀ j) + dist (Y₀ j) (Z j)
      rcases hYj : Y₀ j with a | b
      · have hWj : W j = a := by rw [hW]; simp [hYj]
        rw [hWj]
      · have hWj : W j = X j := by rw [hW]; simp [hYj]
        rw [hWj]
        have htri := dist_triangle (Sum.inl (X j) : M ⊕ M) (Sum.inr b) (Z j)
        have h0 : dist (Sum.inl (X j) : M ⊕ M) (Sum.inl (X j)) = 0 := dist_self _
        rw [h0]
        linarith
    have hmcW : moveCost (fun j => Sum.inl (X j) : Config k (M ⊕ M)) (fun j => Sum.inl (W j))
        = moveCost X W := rfl
    have hlipM := workFnU_lipschitz k hk M C₀ σ' W X
    have hcovW : workFnU C₀ (σ' ++ [r]) W = workFnU C₀ σ' W :=
      wfU_covered k hk M C₀ σ' r W ⟨i, hWr⟩
    have hmcY : @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) Y₀ Z
        = dist (Sum.inl r : M ⊕ M) (Z i) := by
      rw [hY₀]
      exact mc_upd Z i (Sum.inl r)
    refine ⟨W, ?_⟩
    rw [hmap]
    have hrec : workFnU (fun i => Sum.inl (C₀ i) : Config k (M ⊕ M)) (σ'.map Sum.inl) Y₀
        + dist (Sum.inl r : M ⊕ M) (Z i)
        ≤ workFnU (fun i => Sum.inl (C₀ i) : Config k (M ⊕ M))
            (σ'.map Sum.inl ++ [Sum.inl r]) Z := by
      simpa [hY₀] using hi
    rw [hcovW]
    have hchain : workFnU C₀ σ' W
          + moveCost (fun j => Sum.inl (W j) : Config k (M ⊕ M)) Z
        ≤ workFnU (fun i => Sum.inl (C₀ i) : Config k (M ⊕ M)) (σ'.map Sum.inl) Y₀
          + dist (Sum.inl r : M ⊕ M) (Z i) := by
      have h1 : workFnU C₀ σ' W ≤ workFnU C₀ σ' X + moveCost X W := hlipM
      have h2 := hsurg
      rw [hmcW] at h2
      have h3 := hX
      rw [← hmcY]
      linarith
    linarith
end Ext

/-- **The extension work function is the McShane–Lipschitz envelope of the original.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (Z : Config k (M ⊕ M)) :
    (∀ X : Config k M,
      @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) Z
        ≤ workFnU C₀ σ X
          + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (X i)) Z)
    ∧ ∃ X : Config k M,
      @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) Z
        = workFnU C₀ σ X
          + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (X i)) Z := by
  refine ⟨fun X => mcshane_le k hk M Δ hΔ0 hΔ C₀ σ Z X, ?_⟩
  obtain ⟨X, hX⟩ := mcshane_ge k hk M Δ hΔ0 hΔ C₀ σ Z
  exact ⟨X, le_antisymm (mcshane_le k hk M Δ hΔ0 hΔ C₀ σ Z X) hX⟩
