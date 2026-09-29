-- Prove2me | solution 1 for KServer.workFnU_quasiconvex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T08:01:58.408714+00:00
-- url     : https://prove2.me/submissions/687595f8-1e99-4cda-b166-30e2171e31ca

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_nil

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

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

private theorem wfU_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ (Function.update X i r)
  have h1 := wfU_le C₀ (σ ++ [r]) X π
  have h2 := workFn_rec_le k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i)
  rw [← update_comp X i r π] at h2
  have h3 : (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) = X i := by simp
  rw [h3, hπ] at h2
  linarith

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

/-- **Quasiconvexity of the unordered work function.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    ∃ π : Equiv.Perm (Fin k), ∀ s : Finset (Fin k),
      workFnU C₀ σ (fun i => if i ∈ s then X i else Y (π i))
        + workFnU C₀ σ (fun i => if i ∈ s then Y (π i) else X i)
        ≤ workFnU C₀ σ X + workFnU C₀ σ Y := by
  classical
  suffices H : ∀ (τ : List M) (X Y : Config k M), ∃ π : Equiv.Perm (Fin k),
      ∀ s : Finset (Fin k),
        workFnU C₀ τ (fun i => if i ∈ s then X i else Y (π i))
          + workFnU C₀ τ (fun i => if i ∈ s then Y (π i) else X i)
          ≤ workFnU C₀ τ X + workFnU C₀ τ Y from H σ X Y
  intro τ
  induction τ using List.reverseRecOn with
  | nil =>
      intro X Y
      obtain ⟨α, hα⟩ := wfU_exists C₀ ([] : List M) X
      obtain ⟨β, hβ⟩ := wfU_exists C₀ ([] : List M) Y
      refine ⟨β * α⁻¹, fun s => ?_⟩
      have key : ∀ V : Config k M, workFnU C₀ [] V ≤ ∑ j, dist (C₀ j) (V (α j)) := by
        intro V
        have h := wfU_le C₀ ([] : List M) V α
        rw [workFn_nil k hk M C₀ (V ∘ (α : Equiv.Perm (Fin k)))] at h
        simpa [moveCost] using h
      have hX : workFnU C₀ [] X = ∑ j, dist (C₀ j) (X (α j)) := by
        rw [← hα, workFn_nil k hk M C₀ (X ∘ (α : Equiv.Perm (Fin k)))]
        simp [moveCost]
      have hY : workFnU C₀ [] Y = ∑ j, dist (C₀ j) (Y (β j)) := by
        rw [← hβ, workFn_nil k hk M C₀ (Y ∘ (β : Equiv.Perm (Fin k)))]
        simp [moveCost]
      have hval : ∀ j : Fin k, (β * α⁻¹ : Equiv.Perm (Fin k)) (α j) = β j := by
        intro j; simp
      have hZ := key (fun i => if i ∈ s then X i else Y ((β * α⁻¹ : Equiv.Perm (Fin k)) i))
      have hW := key (fun i => if i ∈ s then Y ((β * α⁻¹ : Equiv.Perm (Fin k)) i) else X i)
      simp only [hval] at hZ hW
      have hsum : (∑ j, dist (C₀ j) (if α j ∈ s then X (α j) else Y (β j)))
          + (∑ j, dist (C₀ j) (if α j ∈ s then Y (β j) else X (α j)))
          = (∑ j, dist (C₀ j) (X (α j))) + ∑ j, dist (C₀ j) (Y (β j)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : α j ∈ s
        · simp [h]
        · simp [h]; ring
      rw [hX, hY, ← hsum]
      linarith
  | append_singleton τ r ih =>
      intro X Y
      obtain ⟨i, hi⟩ := wfU_rec_ge k hk M C₀ τ r X
      obtain ⟨j, hj⟩ := wfU_rec_ge k hk M C₀ τ r Y
      obtain ⟨π', hπ'⟩ := ih (Function.update X i r) (Function.update Y j r)
      set ls : Fin k := π'.symm j with hlsdef
      set π : Equiv.Perm (Fin k) := Equiv.swap j (π' i) * π' with hπdef
      refine ⟨π, fun s => ?_⟩
      set X' : Config k M := Function.update X i r with hX'def
      set Y' : Config k M := Function.update Y j r with hY'def
      set Z : Config k M := fun l => if l ∈ s then X l else Y (π l) with hZdef
      set W : Config k M := fun l => if l ∈ s then Y (π l) else X l with hWdef
      -- the values taken by the new permutation
      have hπi : π i = j := by
        rw [hπdef]; simp only [Equiv.Perm.mul_apply]; exact Equiv.swap_apply_right _ _
      have hπls : π ls = π' i := by
        have h1 : π' ls = j := by rw [hlsdef]; exact Equiv.apply_symm_apply π' j
        rw [hπdef]; simp only [Equiv.Perm.mul_apply, h1]; exact Equiv.swap_apply_left _ _
      have hπother : ∀ l : Fin k, l ≠ i → l ≠ ls → π l = π' l := by
        intro l h1 h2
        have e1 : π' l ≠ j := by
          intro hc; exact h2 (by rw [hlsdef, ← hc]; exact (Equiv.symm_apply_apply π' l).symm)
        have e2 : π' l ≠ π' i := fun hc => h1 (π'.injective hc)
        rw [hπdef]; simp only [Equiv.Perm.mul_apply]
        exact Equiv.swap_apply_of_ne_of_ne e1 e2
      have hjls : ∀ l : Fin k, π' l = j → l = ls := by
        intro l hc; rw [hlsdef, ← hc]; exact (Equiv.symm_apply_apply π' l).symm
      -- the two one-step bounds
      have hZle := wfU_rec_le k hk M C₀ τ r Z i
      have hWle := wfU_rec_le k hk M C₀ τ r W i
      have hd : dist r (Z i) + dist r (W i) = dist r (X i) + dist r (Y j) := by
        have hZi : Z i = if i ∈ s then X i else Y j := by simp only [hZdef, hπi]
        have hWi : W i = if i ∈ s then Y j else X i := by simp only [hWdef, hπi]
        rw [hZi, hWi]
        by_cases h : i ∈ s
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]; ring
      set s' : Finset (Fin k) := if ls ∈ s then insert i s else s.erase i with hs'def
      have hIH := hπ' s'
      by_cases hls : ls ∈ s
      · have hs' : s' = insert i s := by rw [hs'def, if_pos hls]
        have hmem : ∀ l : Fin k, l ≠ i → (l ∈ s' ↔ l ∈ s) := by
          intro l hl; rw [hs']; simp [Finset.mem_insert, hl]
        have hZ' : (fun l => if l ∈ s' then X' l else Y' (π' l)) = Function.update Z i r := by
          funext l
          show (if l ∈ s' then X' l else Y' (π' l)) = Function.update Z i r l
          by_cases hli : l = i
          · rw [hli, if_pos (by rw [hs']; exact Finset.mem_insert_self i s), hX'def,
              Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hli]
            by_cases hlS : l ∈ s
            · rw [if_pos ((hmem l hli).mpr hlS), hX'def, Function.update_of_ne hli]
              simp only [hZdef, hlS, if_true]
            · have hlls : l ≠ ls := fun hc => hlS (hc ▸ hls)
              have e1 : π' l ≠ j := fun hc => hlls (hjls l hc)
              rw [if_neg (fun hc => hlS ((hmem l hli).mp hc)), hY'def,
                Function.update_of_ne e1]
              simp only [hZdef, hlS, if_false, hπother l hli hlls]
        have hW' : (fun l => if l ∈ s' then Y' (π' l) else X' l)
            = (Function.update W i r) ∘ (Equiv.swap i ls) := by
          funext l
          show (if l ∈ s' then Y' (π' l) else X' l)
            = Function.update W i r (Equiv.swap i ls l)
          by_cases hli : l = i
          · rw [hli, if_pos (by rw [hs']; exact Finset.mem_insert_self i s),
              Equiv.swap_apply_left]
            by_cases hlsi : ls = i
            · have hsy : π'.symm j = i := by rw [← hlsdef]; exact hlsi
              have hpi : π' i = j := by rw [← hsy]; exact Equiv.apply_symm_apply π' j
              rw [hpi, hY'def, Function.update_self, hlsi, Function.update_self]
            · have e1 : π' i ≠ j := fun hc => hlsi (hjls i hc).symm
              rw [hY'def, Function.update_of_ne e1, Function.update_of_ne hlsi]
              simp only [hWdef, hls, if_true, hπls]
          · by_cases hlls : l = ls
            · rw [hlls, if_pos (by rw [hs']; exact Finset.mem_insert_of_mem hls),
                Equiv.swap_apply_right]
              have e1 : π' ls = j := by rw [hlsdef]; exact Equiv.apply_symm_apply π' j
              rw [e1, hY'def, Function.update_self, Function.update_self]
            · have e1 : π' l ≠ j := fun hc => hlls (hjls l hc)
              rw [Equiv.swap_apply_of_ne_of_ne hli hlls, Function.update_of_ne hli]
              by_cases hlS : l ∈ s
              · rw [if_pos ((hmem l hli).mpr hlS), hY'def, Function.update_of_ne e1]
                simp only [hWdef, hlS, if_true, hπother l hli hlls]
              · rw [if_neg (fun hc => hlS ((hmem l hli).mp hc)), hX'def,
                  Function.update_of_ne hli]
                simp only [hWdef, hlS, if_false]
        rw [hZ', hW'] at hIH
        rw [workFnU_perm k M C₀ τ (Function.update W i r) (Equiv.swap i ls)] at hIH
        linarith
      · have hs' : s' = s.erase i := by rw [hs'def, if_neg hls]
        have hmem : ∀ l : Fin k, l ≠ i → (l ∈ s' ↔ l ∈ s) := by
          intro l hl; rw [hs']; simp [Finset.mem_erase, hl]
        have hW' : (fun l => if l ∈ s' then Y' (π' l) else X' l) = Function.update W i r := by
          funext l
          show (if l ∈ s' then Y' (π' l) else X' l) = Function.update W i r l
          by_cases hli : l = i
          · rw [hli, if_neg (by rw [hs']; simp), hX'def, Function.update_self,
              Function.update_self]
          · rw [Function.update_of_ne hli]
            by_cases hlS : l ∈ s
            · have hlls : l ≠ ls := fun hc => hls (hc ▸ hlS)
              have e1 : π' l ≠ j := fun hc => hlls (hjls l hc)
              rw [if_pos ((hmem l hli).mpr hlS), hY'def, Function.update_of_ne e1]
              simp only [hWdef, hlS, if_true, hπother l hli hlls]
            · rw [if_neg (fun hc => hlS ((hmem l hli).mp hc)), hX'def,
                Function.update_of_ne hli]
              simp only [hWdef, hlS, if_false]
        have hZ' : (fun l => if l ∈ s' then X' l else Y' (π' l))
            = (Function.update Z i r) ∘ (Equiv.swap i ls) := by
          funext l
          show (if l ∈ s' then X' l else Y' (π' l))
            = Function.update Z i r (Equiv.swap i ls l)
          by_cases hli : l = i
          · rw [hli, if_neg (by rw [hs']; simp), Equiv.swap_apply_left]
            by_cases hlsi : ls = i
            · have hsy : π'.symm j = i := by rw [← hlsdef]; exact hlsi
              have hpi : π' i = j := by rw [← hsy]; exact Equiv.apply_symm_apply π' j
              rw [hpi, hY'def, Function.update_self, hlsi, Function.update_self]
            · have e1 : π' i ≠ j := fun hc => hlsi (hjls i hc).symm
              rw [hY'def, Function.update_of_ne e1, Function.update_of_ne hlsi]
              simp only [hZdef, hls, if_false, hπls]
          · by_cases hlls : l = ls
            · rw [hlls, if_neg (by
                rw [hs']; exact fun hc => hls (Finset.mem_of_mem_erase hc)),
                Equiv.swap_apply_right]
              have e1 : π' ls = j := by rw [hlsdef]; exact Equiv.apply_symm_apply π' j
              rw [e1, hY'def, Function.update_self, Function.update_self]
            · have e1 : π' l ≠ j := fun hc => hlls (hjls l hc)
              rw [Equiv.swap_apply_of_ne_of_ne hli hlls, Function.update_of_ne hli]
              by_cases hlS : l ∈ s
              · rw [if_pos ((hmem l hli).mpr hlS), hX'def, Function.update_of_ne hli]
                simp only [hZdef, hlS, if_true]
              · rw [if_neg (fun hc => hlS ((hmem l hli).mp hc)), hY'def,
                  Function.update_of_ne e1]
                simp only [hZdef, hlS, if_false, hπother l hli hlls]
        rw [hZ', hW'] at hIH
        rw [workFnU_perm k M C₀ τ (Function.update Z i r) (Equiv.swap i ls)] at hIH
        linarith
