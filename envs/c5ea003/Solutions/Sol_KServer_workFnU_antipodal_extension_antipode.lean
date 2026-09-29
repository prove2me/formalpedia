-- Prove2me | solution 1 for KServer.workFnU_antipodal_extension_antipode
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-07T17:13:16.187269+00:00
-- url     : https://prove2.me/submissions/2ae96391-be3f-4b39-ae9f-ce9ce01d7bf9

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

/-- The level of a point of the antipodal extension: `0` in the base copy, `1` in the
antipodal copy. -/
private def lev {M : Type} : M ⊕ M → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The projection of the antipodal extension onto the base space along an antipode map. -/
private def proj {M : Type} (a : M → M) : M ⊕ M → M := Sum.elim id a

private theorem lev_nonneg {M : Type} (p : M ⊕ M) : 0 ≤ lev p := by
  cases p <;> simp [lev]

private theorem anti_isom {M : Type} [MetricSpace M] (Δ : ℝ) (a : M → M)
    (ha : ∀ x y : M, dist x (a y) = Δ - dist x y) (x y : M) :
    dist (a x) (a y) = dist x y := by
  have h1 := ha (a x) y
  have h2 := ha y x
  rw [dist_comm y (a x)] at h2
  rw [h1, h2, dist_comm y x]
  ring

/-- The distance of the antipodal extension splits into the base distance of the
projections plus `Δ` for each change of copy. -/
private theorem antiD_split {M : Type} [MetricSpace M] (Δ : ℝ) (a : M → M)
    (ha : ∀ x y : M, dist x (a y) = Δ - dist x y) (p q : M ⊕ M) :
    antiD Δ p q = dist (proj a p) (proj a q) + Δ * |lev p - lev q| := by
  rcases p with x | x <;> rcases q with y | y
  · simp [antiD, proj, lev]
  · have := ha x y
    simp [antiD, proj, lev, this]
    ring
  · have h2 := ha y x
    rw [dist_comm y (a x)] at h2
    simp [antiD, proj, lev, h2, dist_comm y x]
    ring
  · simp [antiD, proj, lev, anti_isom Δ a ha x y]

private theorem finite_ciInf_add {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ℝ) (c : ℝ) :
    (⨅ i, (f i + c)) = (⨅ i, f i) + c := by
  have hb : BddBelow (Set.range f) := Set.Finite.bddBelow (Set.finite_range f)
  have hb' : BddBelow (Set.range fun i => f i + c) := Set.Finite.bddBelow (Set.finite_range _)
  refine le_antisymm ?_ ?_
  · obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := f)
    calc (⨅ i, (f i + c)) ≤ f i0 + c := ciInf_le hb' i0
      _ = (⨅ i, f i) + c := by rw [hi0]
  · refine le_ciInf fun i => ?_
    have := ciInf_le hb i
    linarith

private theorem abs_diff_le_sum (f : ℕ → ℝ) (n : ℕ) :
    |f 0 - f n| ≤ ∑ j ∈ Finset.range n, |f j - f (j + 1)| := by
  induction n with
  | zero => simp
  | succ n ih =>
      have htri : |f 0 - f (n + 1)| ≤ |f 0 - f n| + |f n - f (n + 1)| :=
        abs_sub_le (f 0) (f n) (f (n + 1))
      rw [Finset.sum_range_succ]
      linarith

/-- The labelled work function of the antipodal extension at an arbitrary configuration
of the extension, in terms of the work function of the base space. -/
private theorem lab_barred (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (a : M → M)
    (ha : ∀ x y : M, dist x (a y) = Δ - dist x y)
    (C₀ : Config k M) (σ : List M) (X : Config k (M ⊕ M)) :
    @workFn k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) X
      = workFn C₀ σ (fun i => proj a (X i)) + Δ * ∑ i, lev (X i) := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  have hlen : (σ.map (Sum.inl : M → M ⊕ M)).length = σ.length := by simp
  have hdist : ∀ p q : M ⊕ M, dist p q = dist (proj a p) (proj a q) + Δ * |lev p - lev q| := by
    intro p q; exact antiD_split Δ a ha p q
  -- cost of a schedule in the extension, split server by server
  have hsplit : ∀ (T : ℕ → Config k (M ⊕ M)) (n : ℕ),
      (∑ j ∈ Finset.range n, moveCost (T j) (T (j + 1))) + moveCost (T n) X
        = ((∑ j ∈ Finset.range n, moveCost (fun i => proj a (T j i))
              (fun i => proj a (T (j + 1) i)))
            + moveCost (fun i => proj a (T n i)) (fun i => proj a (X i)))
          + Δ * ∑ i, ((∑ j ∈ Finset.range n, |lev (T j i) - lev (T (j + 1) i)|)
              + |lev (T n i) - lev (X i)|) := by
    intro T n
    have e1 : ∀ j : ℕ, moveCost (T j) (T (j + 1))
        = moveCost (fun i => proj a (T j i)) (fun i => proj a (T (j + 1) i))
          + ∑ i, Δ * |lev (T j i) - lev (T (j + 1) i)| := by
      intro j
      simp only [moveCost, hdist]
      rw [Finset.sum_add_distrib]
    have e2 : moveCost (T n) X
        = moveCost (fun i => proj a (T n i)) (fun i => proj a (X i))
          + ∑ i, Δ * |lev (T n i) - lev (X i)| := by
      simp only [moveCost, hdist]
      rw [Finset.sum_add_distrib]
    have e3 : ∑ j ∈ Finset.range n, ∑ i, Δ * |lev (T j i) - lev (T (j + 1) i)|
        = ∑ i, ∑ j ∈ Finset.range n, Δ * |lev (T j i) - lev (T (j + 1) i)| := Finset.sum_comm
    have e5 : (∑ i, ∑ j ∈ Finset.range n, Δ * |lev (T j i) - lev (T (j + 1) i)|)
          + (∑ i, Δ * |lev (T n i) - lev (X i)|)
        = Δ * ∑ i, ((∑ j ∈ Finset.range n, |lev (T j i) - lev (T (j + 1) i)|)
            + |lev (T n i) - lev (X i)|) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_add, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => e1 j), e2, Finset.sum_add_distrib, e3]
    linarith [e5]
  refine le_antisymm ?_ ?_
  · -- lift a base schedule, adding exactly `Δ` per antipodal server
    rw [workFn_eq, workFn_eq]
    have hkey : ∀ c ∈ Wset C₀ σ (fun i => proj a (X i)),
        sInf (Wset (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) X) ≤ c + Δ * ∑ i, lev (X i) := by
      rintro c ⟨S, hS, rfl⟩
      refine csInf_le (Wset_bdd _ _ _) ⟨fun j i => Sum.inl (S j i), ⟨?_, ?_⟩, ?_⟩
      · funext i
        exact congrArg Sum.inl (congrFun hS.1 i)
      · intro j
        have hj' : j.1 < σ.length := by simpa [hlen] using j.2
        obtain ⟨i, hi⟩ := hS.2 ⟨j.1, hj'⟩
        refine ⟨i, ?_⟩
        show Sum.inl (S (↑j + 1) i) = (σ.map Sum.inl).get j
        rw [List.get_eq_getElem, List.getElem_map]
        exact congrArg Sum.inl (by simpa using hi)
      · rw [hsplit (fun j i => Sum.inl (S j i)) (σ.map (Sum.inl : M → M ⊕ M)).length]
        rw [hlen]
        have hp : ∀ j, (fun i => proj a ((Sum.inl (S j i) : M ⊕ M))) = S j := by
          intro j; funext i; rfl
        simp only [hp]
        have hlev : ∀ (j : ℕ) (i : Fin k), lev (Sum.inl (S j i) : M ⊕ M) = 0 := by
          intro j i; rfl
        simp only [hlev, zero_sub, abs_neg, abs_zero, Finset.sum_const_zero, zero_add]
        simp [abs_of_nonneg (lev_nonneg (X _))]
    have h := le_csInf (Wset_nonempty hk C₀ σ (fun i => proj a (X i)))
      (fun c hc => sub_le_iff_le_add.mpr (hkey c hc))
    linarith
  · -- project any schedule of the extension to the base space
    rw [workFn_eq, workFn_eq]
    have hkey : ∀ c ∈ Wset (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) X,
        sInf (Wset C₀ σ (fun i => proj a (X i))) + Δ * ∑ i, lev (X i) ≤ c := by
      rintro c ⟨T, hT, rfl⟩
      have hs : ServesFrom C₀ σ (fun j i => proj a (T j i)) := by
        constructor
        · funext i
          show proj a (T 0 i) = C₀ i
          rw [congrFun hT.1 i]
          rfl
        · intro j
          have hj' : j.1 < (σ.map (Sum.inl : M → M ⊕ M)).length := by simpa [hlen] using j.isLt
          obtain ⟨i, hi⟩ := hT.2 ⟨j.1, hj'⟩
          refine ⟨i, ?_⟩
          show proj a (T (↑j + 1) i) = σ.get j
          have hi' : T (↑j + 1) i = (σ.map (Sum.inl : M → M ⊕ M)).get ⟨j.1, hj'⟩ := hi
          rw [hi', List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
          rfl
      have hbase : sInf (Wset C₀ σ (fun i => proj a (X i)))
          ≤ (∑ j ∈ Finset.range σ.length, moveCost (fun i => proj a (T j i))
                (fun i => proj a (T (j + 1) i)))
            + moveCost (fun i => proj a (T σ.length i)) (fun i => proj a (X i)) :=
        csInf_le (Wset_bdd _ _ _) ⟨fun j i => proj a (T j i), hs, rfl⟩
      have hT0 : ∀ i : Fin k, lev (T 0 i) = 0 := by
        intro i
        have : T 0 i = Sum.inl (C₀ i) := congrFun hT.1 i
        rw [this]; rfl
      have hlevbound : ∀ i : Fin k, lev (X i)
          ≤ (∑ j ∈ Finset.range σ.length, |lev (T j i) - lev (T (j + 1) i)|)
              + |lev (T σ.length i) - lev (X i)| := by
        intro i
        have h1 : |lev (T 0 i) - lev (T σ.length i)|
            ≤ ∑ j ∈ Finset.range σ.length, |lev (T j i) - lev (T (j + 1) i)| :=
          abs_diff_le_sum (fun j => lev (T j i)) σ.length
        have h2 : |lev (T 0 i) - lev (X i)|
            ≤ |lev (T 0 i) - lev (T σ.length i)| + |lev (T σ.length i) - lev (X i)| :=
          abs_sub_le _ _ _
        have h3 : |lev (T 0 i) - lev (X i)| = lev (X i) := by
          rw [hT0 i, zero_sub, abs_neg, abs_of_nonneg (lev_nonneg (X i))]
        linarith
      have hsum : Δ * ∑ i, lev (X i)
          ≤ Δ * ∑ i : Fin k, ((∑ j ∈ Finset.range σ.length, |lev (T j i) - lev (T (j + 1) i)|)
              + |lev (T σ.length i) - lev (X i)|) := by
        have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hlevbound i)
        exact mul_le_mul_of_nonneg_left this (le_of_lt hΔ0)
      rw [hsplit T (σ.map (Sum.inl : M → M ⊕ M)).length, hlen]
      linarith
    exact le_csInf (Wset_nonempty hk _ _ _) hkey

/-- **The unordered work function of the antipodal extension at a configuration with
antipodal servers.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (a : M → M)
    (ha : ∀ x y : M, dist x (a y) = Δ - dist x y)
    (C₀ : Config k M) (σ : List M) (X : Config k (M ⊕ M)) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) X
      = workFnU C₀ σ (fun i => Sum.elim id a (X i))
        + Δ * ∑ i, Sum.elim (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) (X i) := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  have hlev : ∀ p : M ⊕ M, Sum.elim (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) p = lev p := fun p => rfl
  simp only [hlev]
  unfold workFnU
  have hcomp : ∀ π : Equiv.Perm (Fin k),
      @workFn k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (X ∘ π)
        = workFn C₀ σ ((fun i => proj a (X i)) ∘ π) + Δ * ∑ i, lev (X i) := by
    intro π
    have h := lab_barred k hk M Δ hΔ0 hΔ a ha C₀ σ (X ∘ π)
    have hperm : ∑ i, lev ((X ∘ π) i) = ∑ i, lev (X i) := Equiv.sum_comp π (fun i => lev (X i))
    rw [hperm] at h
    exact h
  have : ∀ π : Equiv.Perm (Fin k),
      @workFn k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (X ∘ π)
        = (fun π : Equiv.Perm (Fin k) =>
            workFn C₀ σ ((fun i => proj a (X i)) ∘ π)) π + Δ * ∑ i, lev (X i) := hcomp
  simp only [this]
  exact finite_ciInf_add _ _

