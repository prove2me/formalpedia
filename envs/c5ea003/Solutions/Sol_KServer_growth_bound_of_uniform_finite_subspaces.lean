-- Prove2me | solution 1 for KServer.growth_bound_of_uniform_finite_subspaces
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:43:39.070238+00:00
-- url     : https://prove2.me/submissions/1516e7e5-43b0-486a-9f28-0267a680663f

import Theorems.Thm_KServer_workFnU_isometry_embedding

set_option autoImplicit false
open KServer

private lemma sum_sup_le {I : Type} [Nonempty I] (s : Finset ℕ)
    (f : ℕ → I → ℝ) (B : ℝ)
    (H : ∀ x : ℕ → I, (∑ t ∈ s, f t (x t)) ≤ B) :
    (∑ t ∈ s, sSup (Set.range (f t))) ≤ B := by
  classical
  induction s using Finset.induction_on generalizing B with
  | empty => simpa using H (fun _ => Classical.choice ‹Nonempty I›)
  | @insert t s ht ih =>
    have htail (a : I) : (∑ j ∈ s, sSup (Set.range (f j))) ≤ B - f t a := by
      apply ih
      intro x
      have h := H (Function.update x t a)
      rw [Finset.sum_insert ht] at h
      have hh : (∑ j ∈ s, f j (Function.update x t a j)) = ∑ j ∈ s, f j (x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (by intro h; subst j; exact ht hj)]
      rw [Function.update_self, hh] at h
      linarith
    have hhead : sSup (Set.range (f t)) ≤ B - ∑ j ∈ s, sSup (Set.range (f j)) := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨a, rfl⟩
      linarith [htail a]
    rw [Finset.sum_insert ht]
    linarith

private lemma cost_nonneg {k : ℕ} {M : Type} [MetricSpace M]
    (C D : Config k M) : 0 ≤ moveCost C D :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

private lemma exists_schedule (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C : Config k M) (σ : List M) : ∃ S, ServesFrom C σ S := by
  let S : ℕ → Config k M := fun t i => if t = 0 then C i else σ[t - 1]?.getD (C i)
  refine ⟨S, ?_, ?_⟩
  · funext i
    simp [S]
  · intro j
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [S, List.get_eq_getElem]

private lemma sampled_bound (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (a c : ℝ) (ha : 0 < a)
    (H : ∀ (P : Finset M) (D₀ : Config k P),
      (∀ i, (D₀ i : M) = C₀ i) → ∀ τ : List P, ∃ u : ℕ → ℝ,
        (∀ t, t < τ.length → ∀ Y : Config k P, Function.Injective Y →
          workFnU D₀ (τ.take (t + 1)) Y ≤ workFnU D₀ (τ.take t) Y + u t) ∧
        (∑ t ∈ Finset.range τ.length, u t) ≤ a * offlineCost D₀ τ + c)
    (σ : List M) (X : ℕ → {X : Config k M // Function.Injective X}) :
    (∑ t ∈ Finset.range σ.length,
      (workFnU C₀ (σ.take (t + 1)) (X t).val - workFnU C₀ (σ.take t) (X t).val))
      ≤ a * offlineCost C₀ σ + c := by
  classical
  let z := ∑ t ∈ Finset.range σ.length,
      (workFnU C₀ (σ.take (t + 1)) (X t).val - workFnU C₀ (σ.take t) (X t).val)
  have hSbound (S : ℕ → Config k M) (hS : ServesFrom C₀ σ S) :
      z ≤ a * (∑ t ∈ Finset.range σ.length, moveCost (S t) (S (t + 1))) + c := by
    let P : Finset M := Finset.univ.image C₀ ∪ σ.toFinset ∪
      (Finset.range σ.length).biUnion (fun t => Finset.univ.image (X t).val) ∪
      (Finset.range (σ.length + 1)).biUnion (fun t => Finset.univ.image (S t))
    have hC (i : Fin k) : C₀ i ∈ P := by
      simp only [P, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
    have hσ (r : M) (hr : r ∈ σ) : r ∈ P := by
      simp only [P, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr (List.mem_toFinset.mpr hr)))
    have hX (t : ℕ) (ht : t < σ.length) (i : Fin k) : (X t).val i ∈ P := by
      simp only [P, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_biUnion.mpr ⟨t, Finset.mem_range.mpr ht,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩))
    have hSp (t : ℕ) (ht : t ≤ σ.length) (i : Fin k) : S t i ∈ P := by
      simp only [P, Finset.mem_union]
      exact Or.inr (Finset.mem_biUnion.mpr ⟨t, Finset.mem_range.mpr (by omega),
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    let lift : M → P := fun x => if h : x ∈ P then ⟨x, h⟩ else ⟨C₀ ⟨0, by omega⟩, hC _⟩
    have hlift (x : M) (hx : x ∈ P) : (lift x : M) = x := by simp [lift, hx]
    let D₀ : Config k P := fun i => lift (C₀ i)
    let τ : List P := σ.map lift
    let T : ℕ → Config k P := fun t i => lift (S t i)
    have hD₀ : (fun i => (D₀ i : M)) = C₀ := funext fun i => hlift _ (hC i)
    have hτ : τ.map (fun x : P => (x : M)) = σ := by
      dsimp only [τ]
      rw [List.map_map]
      exact List.map_congr_left (fun x hx => hlift x (hσ x hx)) |>.trans (List.map_id σ)
    have hT (t : ℕ) (ht : t ≤ σ.length) : (fun i => (T t i : M)) = S t :=
      funext fun i => hlift _ (hSp t ht i)
    have hserve : ServesFrom D₀ τ T := by
      constructor
      · dsimp only [T, D₀]
        rw [hS.1]
      · intro j
        obtain ⟨i, hi⟩ := hS.2 ⟨j.val, by simpa [τ] using j.isLt⟩
        refine ⟨i, ?_⟩
        simpa [T, τ, List.get_eq_getElem, hi] using congrArg lift hi
    have hcost : (∑ t ∈ Finset.range τ.length, moveCost (T t) (T (t + 1))) =
        ∑ t ∈ Finset.range σ.length, moveCost (S t) (S (t + 1)) := by
      simp only [τ, List.length_map]
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_range.mp ht
      change (∑ i, dist ((T t i : P) : M) ((T (t + 1) i : P) : M)) = _
      change moveCost (fun i => (T t i : M)) (fun i => (T (t + 1) i : M)) = _
      rw [hT t (by omega), hT (t + 1) (by omega)]
    have hoff : offlineCost D₀ τ ≤ ∑ t ∈ Finset.range σ.length, moveCost (S t) (S (t + 1)) := by
      rw [← hcost]
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro v ⟨U, _, rfl⟩
        exact Finset.sum_nonneg fun _ _ => cost_nonneg _ _
      · exact ⟨T, hserve, rfl⟩
    obtain ⟨u, hu, hsum⟩ := H P D₀ (fun i => congrFun hD₀ i) τ
    have hinc (t : ℕ) (ht : t < σ.length) :
        workFnU C₀ (σ.take (t + 1)) (X t).val - workFnU C₀ (σ.take t) (X t).val ≤ u t := by
      let Y : Config k P := fun i => lift ((X t).val i)
      have hY : (fun i => (Y i : M)) = (X t).val := funext fun i => hlift _ (hX t ht i)
      have hYi : Function.Injective Y := by
        intro i j hij
        apply (X t).property
        have heq := congrArg (fun x : P => (x : M)) hij
        simpa only [← hY] using heq
      have hw (n : ℕ) : workFnU D₀ (τ.take n) Y = workFnU C₀ (σ.take n) (X t).val := by
        have hh := KServer.workFnU_isometry_embedding k hk P M (fun x => (x : M))
          (fun _ _ => rfl) D₀ (τ.take n) Y
        rw [hD₀, List.map_take, hτ, hY] at hh
        exact hh.symm
      have hh := hu t (by simpa [τ] using ht) Y hYi
      rw [hw, hw] at hh
      linarith
    have hz : z ≤ ∑ t ∈ Finset.range σ.length, u t :=
      Finset.sum_le_sum fun t ht => hinc t (Finset.mem_range.mp ht)
    simp only [τ, List.length_map] at hsum
    have hm := mul_le_mul_of_nonneg_left hoff ha.le
    dsimp only [τ] at hm
    linarith
  obtain ⟨S₀, hS₀⟩ := exists_schedule k hk M C₀ σ
  have hinf : (z - c) / a ≤ offlineCost C₀ σ := by
    apply le_csInf
    · exact ⟨_, S₀, hS₀, rfl⟩
    · rintro v ⟨S, hS, rfl⟩
      apply (div_le_iff₀ ha).mpr
      linarith [hSbound S hS]
  have hh := (div_le_iff₀ ha).mp hinf
  dsimp only [z] at hh
  linarith

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (a c : ℝ) (ha : 0 < a)
    (hI : ∃ X : Config k M, Function.Injective X)
    (H : ∀ (P : Finset M) (D₀ : Config k P),
      (∀ i, (D₀ i : M) = C₀ i) → ∀ τ : List P, ∃ u : ℕ → ℝ,
        (∀ t, t < τ.length → ∀ Y : Config k P, Function.Injective Y →
          workFnU D₀ (τ.take (t + 1)) Y ≤ workFnU D₀ (τ.take t) Y + u t) ∧
        (∑ t ∈ Finset.range τ.length, u t) ≤ a * offlineCost D₀ τ + c) :
    ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t, t < σ.length → ∀ X : Config k M, Function.Injective X →
        workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ a * offlineCost C₀ σ + c := by
  classical
  let I := {X : Config k M // Function.Injective X}
  letI : Nonempty I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
  intro σ
  let f (t : ℕ) (X : I) := workFnU C₀ (σ.take (t + 1)) X.val - workFnU C₀ (σ.take t) X.val
  let B := a * offlineCost C₀ σ + c
  have Hchoice (X : ℕ → I) : (∑ t ∈ Finset.range σ.length, f t (X t)) ≤ B :=
    sampled_bound k hk M C₀ a c ha H σ X
  let X₀ : I := Classical.choice ‹Nonempty I›
  have hb (t : ℕ) (ht : t < σ.length) : BddAbove (Set.range (f t)) := by
    refine ⟨B - ∑ j ∈ (Finset.range σ.length).erase t, f j X₀, ?_⟩
    rintro _ ⟨X, rfl⟩
    have hh := Hchoice (Function.update (fun _ => X₀) t X)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr ht), Function.update_self] at hh
    have heq : (∑ j ∈ (Finset.range σ.length).erase t,
        f j (Function.update (fun _ => X₀) t X j)) =
        ∑ j ∈ (Finset.range σ.length).erase t, f j X₀ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [heq] at hh
    linarith
  refine ⟨fun t => sSup (Set.range (f t)), ?_, ?_⟩
  · intro t ht X hX
    have hh := le_csSup (hb t ht) (Set.mem_range_self (f := f t) (⟨X, hX⟩ : I))
    dsimp only [f] at hh
    linarith
  · apply sum_sup_le
    exact Hchoice

#print axioms solution
