-- Prove2me | solution 1 for KServer.workFnU_injective_witness
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T20:28:58.686405+00:00
-- url     : https://prove2.me/submissions/2aef50e6-3fad-4c61-9a05-9ef01d4bca67

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_step_le
import Theorems.Thm_KServer_workFnU_step_approx
import Theorems.Thm_KServer_moveCost_injective_between
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_workFnU_perm

namespace KServer

variable {k : ℕ} {M : Type} [MetricSpace M]

theorem moveCost_comm (X Y : Config k M) : moveCost X Y = moveCost Y X := by
  unfold moveCost
  exact Finset.sum_congr rfl fun i _ => dist_comm _ _

theorem moveCost_triangle (X Y Z : Config k M) :
    moveCost X Z ≤ moveCost X Y + moveCost Y Z := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

theorem moveCost_nonneg (X Y : Config k M) : 0 ≤ moveCost X Y :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

theorem moveCost_self (X : Config k M) : moveCost X X = 0 := by
  unfold moveCost; simp

/-- With the initial configuration as target, the empty-history work function vanishes. -/
theorem workFnU_nil_start (hk : 1 ≤ k) (C₀ : Config k M) :
    workFnU C₀ [] C₀ = 0 := by
  have hbdd : BddBelow (Set.range fun π : Equiv.Perm (Fin k) => workFn C₀ [] (C₀ ∘ π)) :=
    (Set.finite_range _).bddBelow
  have hle : workFnU C₀ [] C₀ ≤ 0 := by
    have h := ciInf_le hbdd (Equiv.refl (Fin k))
    have he : workFn C₀ [] (C₀ ∘ (Equiv.refl (Fin k))) = 0 := by
      rw [workFn_nil k hk M C₀]
      simpa using moveCost_self (k := k) (M := M) C₀
    rw [he] at h
    exact h
  have hge : (0:ℝ) ≤ workFnU C₀ [] C₀ := by
    refine le_ciInf fun π => ?_
    rw [workFn_nil k hk M C₀]
    exact moveCost_nonneg _ _
  linarith

/-- **Base case of the witness lemma.** -/
theorem witness_nil (hk : 1 ≤ k) (C₀ : Config k M) (hC₀ : Function.Injective C₀)
    (Y : Config k M) (ε : ℝ) (hε : 0 < ε) :
    ∃ X : Config k M, Function.Injective X ∧
      workFnU C₀ [] X + moveCost X Y ≤ workFnU C₀ [] Y + ε := by
  have hlt : workFnU C₀ [] Y < workFnU C₀ [] Y + ε := by linarith
  obtain ⟨π, hπ⟩ := exists_lt_of_ciInf_lt hlt
  refine ⟨C₀ ∘ (π.symm : Equiv.Perm (Fin k)), hC₀.comp (Equiv.injective _), ?_⟩
  have h1 : workFnU C₀ [] (C₀ ∘ (π.symm : Equiv.Perm (Fin k))) = 0 := by
    rw [workFnU_perm k M C₀ [] C₀ π.symm]
    exact workFnU_nil_start hk C₀
  have h2 : moveCost (C₀ ∘ (π.symm : Equiv.Perm (Fin k))) Y = workFn C₀ [] (Y ∘ π) := by
    rw [workFn_nil k hk M C₀]
    unfold moveCost
    refine (Equiv.sum_comp π (fun j => dist (C₀ (π.symm j)) (Y j))).symm.trans ?_
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [h1, h2, zero_add]
  linarith

/-- **The witness lemma.** If the initial configuration is injective, then at every
history the unordered work function is, up to an arbitrarily small error, the
inf-convolution of its restriction to injective configurations. -/
theorem workFnU_inj_witness_aux (hk : 1 ≤ k) (C₀ : Config k M)
    (hC₀ : Function.Injective C₀) :
    ∀ (σ : List M) (Y : Config k M) (ε : ℝ), 0 < ε →
      ∃ X : Config k M, Function.Injective X ∧
        workFnU C₀ σ X + moveCost X Y ≤ workFnU C₀ σ Y + ε := by
  intro σ
  induction σ using List.reverseRecOn with
  | nil => exact fun Y ε hε => witness_nil hk C₀ hC₀ Y ε hε
  | append_singleton σ r ih =>
    intro Y ε hε
    have hε2 : 0 < ε / 2 := by linarith
    -- the step recurrence: an almost optimal predecessor `Z` covering the request
    obtain ⟨Z, hZr, hZ⟩ := workFnU_step_approx k hk M C₀ σ r Y (ε / 2) hε2
    -- the inductive hypothesis at `Z`
    obtain ⟨X₁, hX₁inj, hX₁⟩ := ih Z (ε / 2) hε2
    -- an injective configuration covering the request, on the way from `Z` to `X₁`
    obtain ⟨X, hXinj, hXr, hXmid⟩ :=
      moveCost_injective_between k M Z X₁ hX₁inj r hZr
    refine ⟨X, hXinj, ?_⟩
    have hstep : workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ X := by
      have h := workFnU_step_le k hk M C₀ σ r X X hXr
      simpa [moveCost_self] using h
    have hlip : workFnU C₀ σ X ≤ workFnU C₀ σ X₁ + moveCost X₁ X :=
      workFnU_lipschitz k hk M C₀ σ X X₁
    have htri : moveCost X Y ≤ moveCost X Z + moveCost Z Y := moveCost_triangle X Z Y
    have hmid : moveCost X₁ X + moveCost X Z ≤ moveCost X₁ Z := by
      have h1 : moveCost X₁ X = moveCost X X₁ := moveCost_comm _ _
      have h2 : moveCost X Z = moveCost Z X := moveCost_comm _ _
      have h3 : moveCost X₁ Z = moveCost Z X₁ := moveCost_comm _ _
      rw [h1, h2, h3]
      linarith [hXmid]
    linarith

/-- **Transfer principle.** With an injective initial configuration, a one-step growth
bound valid at all *injective* configurations is valid at *all* configurations. -/
theorem workFnU_growth_transfer (hk : 1 ≤ k) (C₀ : Config k M)
    (hC₀ : Function.Injective C₀) (σ₁ σ₂ : List M) (u : ℝ)
    (h : ∀ X : Config k M, Function.Injective X →
        workFnU C₀ σ₂ X ≤ workFnU C₀ σ₁ X + u) :
    ∀ X : Config k M, workFnU C₀ σ₂ X ≤ workFnU C₀ σ₁ X + u := by
  intro Y
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨X, hXinj, hX⟩ := workFnU_inj_witness_aux hk C₀ hC₀ σ₁ Y ε hε
  have hlip : workFnU C₀ σ₂ Y ≤ workFnU C₀ σ₂ X + moveCost X Y :=
    workFnU_lipschitz k hk M C₀ σ₂ Y X
  have hgr := h X hXinj
  linarith

end KServer

open KServer

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (hC₀ : Function.Injective C₀) (σ : List M) (Y : Config k M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X : Config k M, Function.Injective X ∧
      workFnU C₀ σ X + moveCost X Y ≤ workFnU C₀ σ Y + ε :=
  KServer.workFnU_inj_witness_aux hk C₀ hC₀ σ Y ε hε
