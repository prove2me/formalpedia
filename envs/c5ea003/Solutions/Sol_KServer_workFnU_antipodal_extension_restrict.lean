-- Prove2me | solution 1 for KServer.workFnU_antipodal_extension_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T05:35:21.194434+00:00
-- url     : https://prove2.me/submissions/b16478cb-d6f7-43c1-85fb-118f48367d4b

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

open KServer

private theorem mc_nonneg {k : ℕ} {N : Type} [MetricSpace N] (A B : Config k N) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun _ _ => dist_nonneg

private def Wset {k : ℕ} {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (X : Config k N) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k N, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem workFn_eq {k : ℕ} {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (X : Config k N) :
    workFn C₀ σ X = sInf (Wset C₀ σ X) := rfl

private theorem Wset_bdd {k : ℕ} {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (X : Config k N) : BddBelow (Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => mc_nonneg _ _
  have h2 := mc_nonneg (S σ.length) X
  linarith

private theorem sched_exists {k : ℕ} (hk : 1 ≤ k) {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) : ∃ S : ℕ → Config k N, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private theorem Wset_nonempty {k : ℕ} (hk : 1 ≤ k) {N : Type} [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (X : Config k N) : (Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sched_exists hk C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

/-- The labelled work function of the antipodal extension restricts to the original. -/
private theorem lab_restrict (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    @workFn k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (fun i => Sum.inl (X i))
      = workFn C₀ σ X := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set pj : M ⊕ M → M := Sum.elim id id with hpj
  have dproj : ∀ p q : M ⊕ M, dist (pj p) (pj q) ≤ dist p q := by
    rintro (x | x) (y | y)
    · exact le_of_eq rfl
    · show dist x y ≤ 2 * Δ - dist x y
      linarith [hΔ x y]
    · show dist x y ≤ 2 * Δ - dist x y
      linarith [hΔ x y]
    · exact le_of_eq rfl
  have mcl : ∀ A B : Config k M,
      moveCost (fun i => Sum.inl (A i) : Config k (M ⊕ M)) (fun i => Sum.inl (B i))
        = moveCost A B := fun A B => rfl
  have mcp : ∀ P Q : Config k (M ⊕ M),
      moveCost (fun i => pj (P i)) (fun i => pj (Q i)) ≤ moveCost P Q := by
    intro P Q
    exact Finset.sum_le_sum fun i _ => dproj (P i) (Q i)
  have hlen : (σ.map (Sum.inl : M → M ⊕ M)).length = σ.length := by simp
  refine le_antisymm ?_ ?_
  · -- extension ≤ original: an M-schedule is an extension schedule of the same cost
    rw [workFn_eq, workFn_eq]
    refine csInf_le_csInf (Wset_bdd _ _ _) (Wset_nonempty hk C₀ σ X) ?_
    rintro c ⟨S, hS, rfl⟩
    refine ⟨fun j i => Sum.inl (S j i), ⟨?_, ?_⟩, ?_⟩
    · funext i
      exact congrArg Sum.inl (congrFun hS.1 i)
    · intro j
      have hj' : j.1 < σ.length := by simpa [hlen] using j.2
      obtain ⟨i, hi⟩ := hS.2 ⟨j.1, hj'⟩
      refine ⟨i, ?_⟩
      show Sum.inl (S (↑j + 1) i) = (σ.map Sum.inl).get j
      rw [List.get_eq_getElem, List.getElem_map]
      exact congrArg Sum.inl (by simpa using hi)
    · rw [hlen]
      rw [mcl (S σ.length) X]
      exact congrArg (fun s => s + moveCost (S σ.length) X)
        (Finset.sum_congr rfl fun j _ => (mcl (S j) (S (j + 1))))
  · -- original ≤ extension: project any extension schedule to M
    rw [workFn_eq, workFn_eq]
    refine le_csInf (Wset_nonempty hk _ _ _) ?_
    rintro c ⟨T, hT, rfl⟩
    have hs : ServesFrom C₀ σ (fun j i => pj (T j i)) := by
      constructor
      · funext i
        show pj (T 0 i) = C₀ i
        rw [congrFun hT.1 i]
        rfl
      · intro j
        have hj' : j.1 < (σ.map (Sum.inl : M → M ⊕ M)).length := by simpa [hlen] using j.2
        obtain ⟨i, hi⟩ := hT.2 ⟨j.1, hj'⟩
        refine ⟨i, ?_⟩
        show pj (T (↑j + 1) i) = σ.get j
        have hi' : T (↑j + 1) i = (σ.map (Sum.inl : M → M ⊕ M)).get ⟨j.1, hj'⟩ := hi
        rw [hi', List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
        rfl
    have hval : (∑ j ∈ Finset.range σ.length,
          moveCost (fun i => pj (T j i)) (fun i => pj (T (j+1) i)))
        + moveCost (fun i => pj (T σ.length i)) X
        ≤ (∑ j ∈ Finset.range (σ.map (Sum.inl : M → M ⊕ M)).length, moveCost (T j) (T (j + 1)))
          + moveCost (T (σ.map (Sum.inl : M → M ⊕ M)).length) (fun i => Sum.inl (X i)) := by
      -- termwise by 1-Lipschitzness of the projection
      rw [hlen]
      have h1 : ∀ j, moveCost (fun i => pj (T j i)) (fun i => pj (T (j+1) i))
          ≤ moveCost (T j) (T (j+1)) := fun j => mcp _ _
      have h2 : moveCost (fun i => pj (T σ.length i)) X ≤ moveCost (T σ.length) (fun i => Sum.inl (X i)) := by
        have := mcp (T σ.length) (fun i => Sum.inl (X i))
        simpa using this
      have hsum : (∑ j ∈ Finset.range σ.length,
            moveCost (fun i => pj (T j i)) (fun i => pj (T (j+1) i)))
          ≤ ∑ j ∈ Finset.range σ.length, moveCost (T j) (T (j + 1)) :=
        Finset.sum_le_sum fun j _ => h1 j
      linarith [h2, hsum]
    refine le_trans (csInf_le (Wset_bdd _ _ _) ⟨fun j i => pj (T j i), hs, rfl⟩) hval

/-- **The work function of the antipodal extension restricts to the original work function.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (fun i => Sum.inl (X i))
      = workFnU C₀ σ X := by
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  unfold workFnU
  refine iInf_congr fun π => ?_
  have h : ((fun i => Sum.inl (X i) : Config k (M ⊕ M)) ∘ π)
      = (fun i => Sum.inl ((X ∘ π) i)) := rfl
  rw [h]
  exact lab_restrict k hk M Δ hΔ0 hΔ C₀ σ (X ∘ π)
