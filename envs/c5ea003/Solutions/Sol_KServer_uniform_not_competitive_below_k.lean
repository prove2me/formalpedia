-- Prove2me | solution 1 for KServer.uniform_not_competitive_below_k
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-09T09:35:34.440412+00:00
-- url     : https://prove2.me/submissions/bc55a7da-0709-48e6-a23d-e0ebca0a675c

import Definitions.Def_KServer_model

namespace KServerLB

open KServer Finset

variable {k : ℕ} {M : Type*} [MetricSpace M]

theorem moveCost_nonneg (C C' : Config k M) : 0 ≤ moveCost C C' :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

@[simp] theorem moveCost_self (C : Config k M) : moveCost C C = 0 := by
  simp [moveCost]

theorem moveCost_le_of_forall_le {C C' : Config k M} {b : ℝ}
    (h : ∀ i, dist (C i) (C' i) ≤ b) : moveCost C C' ≤ k * b := by
  classical
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  simpa [moveCost, Finset.sum_const, mul_comm] using this

/-- The set whose infimum defines `offlineCost`. -/
def offlineCostSet (C₀ : Config k M) (σ : List M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))}

theorem offlineCost_eq_sInf (C₀ : Config k M) (σ : List M) :
    offlineCost C₀ σ = sInf (offlineCostSet C₀ σ) := rfl

theorem offlineCostSet_bddBelow (C₀ : Config k M) (σ : List M) :
    BddBelow (offlineCostSet C₀ σ) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _

theorem offlineCostSet_nonempty (h0 : 0 < k) (C₀ : Config k M) (σ : List M) :
    (offlineCostSet C₀ σ).Nonempty := by
  classical
  -- move server `0` to the current request, all other servers stay at `C₀`
  refine ⟨_, ⟨fun j => if j = 0 then C₀ else (fun i => if i = ⟨0, h0⟩ then
      (if hj : j - 1 < σ.length then σ.get ⟨j - 1, hj⟩ else C₀ i) else C₀ i),
    ⟨by simp, ?_⟩, rfl⟩⟩
  intro j
  refine ⟨⟨0, h0⟩, ?_⟩
  have h1 : (j : ℕ) + 1 - 1 = (j : ℕ) := by omega
  simp [h1, j.isLt]

theorem offlineCost_le {C₀ : Config k M} {σ : List M} {S : ℕ → Config k M}
    (hS : ServesFrom C₀ σ S) :
    offlineCost C₀ σ ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
  csInf_le (offlineCostSet_bddBelow C₀ σ) ⟨S, hS, rfl⟩

theorem offlineCost_nonneg (C₀ : Config k M) (σ : List M) : 0 ≤ offlineCost C₀ σ := by
  refine Real.sInf_nonneg ?_
  rintro c ⟨S, -, rfl⟩
  exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _

theorem cost_nonneg (A : OnlineAlgorithm k M) (σ : List M) : 0 ≤ A.cost σ :=
  Finset.sum_nonneg fun _ _ => moveCost_nonneg _ _

section Index

variable {k : ℕ}

/-- The canonical injection `Fin k → Fin (k+1)` whose image misses `m`. -/
def finComplCfg (m : Fin (k + 1)) : Fin k → Fin (k + 1) := fun i =>
  if (i : ℕ) < (m : ℕ) then ⟨(i : ℕ), by omega⟩ else ⟨(i : ℕ) + 1, by omega⟩

theorem finComplCfg_injective (m : Fin (k + 1)) : Function.Injective (finComplCfg m) := by
  intro a b hab
  have := congrArg (fun x : Fin (k + 1) => x.val) hab
  simp only [finComplCfg] at this
  by_cases ha : (a : ℕ) < (m : ℕ) <;> by_cases hb : (b : ℕ) < (m : ℕ) <;>
    simp [ha, hb] at this <;> exact Fin.ext (by omega)

theorem finComplCfg_ne (m : Fin (k + 1)) (i : Fin k) : finComplCfg m i ≠ m := by
  intro h
  have := congrArg (fun x : Fin (k + 1) => x.val) h
  simp only [finComplCfg] at this
  by_cases hi : (i : ℕ) < (m : ℕ) <;> simp [hi] at this <;> omega

/-- An injection `Fin k → Fin (k+1)` avoiding `m` takes every other value. -/
theorem fin_covers_of_inj {C : Fin k → Fin (k + 1)} {m : Fin (k + 1)}
    (hinj : Function.Injective C) (hm : ∀ i, C i ≠ m) {p : Fin (k + 1)} (hp : p ≠ m) :
    ∃ i, C i = p := by
  classical
  have hsub : Finset.univ.image C ⊆ (Finset.univ : Finset (Fin (k + 1))).erase m := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact Finset.mem_erase.2 ⟨hm i, Finset.mem_univ _⟩
  have hcard : ((Finset.univ : Finset (Fin (k + 1))).erase m).card ≤
      (Finset.univ.image C).card := by
    rw [Finset.card_image_of_injective _ hinj]
    simp [Finset.card_erase_of_mem]
  have heq : Finset.univ.image C = (Finset.univ : Finset (Fin (k + 1))).erase m :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hpmem : p ∈ Finset.univ.image C := by
    rw [heq]; exact Finset.mem_erase.2 ⟨hp, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hpmem
  exact ⟨i, hi⟩

/-- Any `k`-tuple of indices in `Fin (k+1)` misses some value. -/
theorem fin_exists_not_mem_image {ι : Type*} [Fintype ι] (hcard : Fintype.card ι ≤ k)
    (f : ι → Fin (k + 1)) : ∃ p : Fin (k + 1), ∀ i, f i ≠ p := by
  classical
  have h : ∃ p : Fin (k + 1), p ∉ Finset.univ.image f := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆ Finset.univ.image f := fun p _ => hcon p
    have h1 := Finset.card_le_card hsub
    have h2 : (Finset.univ.image f).card ≤ k :=
      le_trans (Finset.card_image_le) (by simpa using hcard)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun i hi => hp (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩)⟩

end Index

open Finset

variable {k : ℕ} {M : Type*} [MetricSpace M]

section Distances

variable (hd : ∀ x y : M, x ≠ y → dist x y = 1)

include hd

theorem uniform_dist_le_one (x y : M) : dist x y ≤ 1 := by
  by_cases h : x = y
  · simp [h]
  · rw [hd x y h]

theorem uniform_moveCost_le (C C' : Config k M) : moveCost C C' ≤ k :=
  (moveCost_le_of_forall_le fun i => uniform_dist_le_one hd (C i) (C' i)).trans (by simp)

end Distances

section Adversary

/-- With `k` servers on `k + 1` points, some point is always uncovered. -/
theorem exists_uncovered (e : Fin (k + 1) ≃ M) (A : OnlineAlgorithm k M)
    (l : List M) : ∃ p, ∀ i, A.conf l i ≠ p := by
  obtain ⟨j, hj⟩ :=
    fin_exists_not_mem_image (ι := Fin k) (by simp) (fun i => e.symm (A.conf l i))
  exact ⟨e j, fun i hi => hj i (by simp [hi])⟩

/-- The point requested by the adversary after the algorithm has seen `l`:
a point currently not covered by the algorithm. -/
noncomputable def advPt (e : Fin (k + 1) ≃ M) (A : OnlineAlgorithm k M) (l : List M) : M :=
  (exists_uncovered e A l).choose

theorem advPt_not_covered (e : Fin (k + 1) ≃ M) (A : OnlineAlgorithm k M) (l : List M)
    (i : Fin k) : A.conf l i ≠ advPt e A l :=
  (exists_uncovered e A l).choose_spec i

/-- The adversary request sequence of length `n` against the algorithm `A`. -/
noncomputable def adv (e : Fin (k + 1) ≃ M) (A : OnlineAlgorithm k M) : ℕ → List M
  | 0 => []
  | n + 1 => adv e A n ++ [advPt e A (adv e A n)]

@[simp] theorem adv_zero (e : Fin (k + 1) ≃ M) (A : OnlineAlgorithm k M) : adv e A 0 = [] := rfl

theorem adv_succ (e : Fin (k + 1) ≃ M) (A : OnlineAlgorithm k M) (n : ℕ) :
    adv e A (n + 1) = adv e A n ++ [advPt e A (adv e A n)] := rfl

@[simp] theorem adv_length (e : Fin (k + 1) ≃ M) (A : OnlineAlgorithm k M) (n : ℕ) :
    (adv e A n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [adv_succ, ih]

theorem adv_take (e : Fin (k + 1) ≃ M) (A : OnlineAlgorithm k M) {n j : ℕ} (h : j ≤ n) :
    (adv e A n).take j = adv e A j := by
  induction n with
  | zero =>
    interval_cases j
    rfl
  | succ n ih =>
    rcases Nat.lt_or_ge j (n + 1) with hj | hj
    · have hjn : j ≤ n := by omega
      rw [adv_succ, List.take_append_of_le_length (by simpa using hjn)]
      exact ih hjn
    · have : j = n + 1 := by omega
      subst this
      simp [List.take_of_length_le]

/-- The algorithm pays at least `1` for each adversary request. -/
theorem one_le_step_cost (hd : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin (k + 1) ≃ M)
    (A : OnlineAlgorithm k M) (j : ℕ) :
    (1 : ℝ) ≤ moveCost (A.conf (adv e A j)) (A.conf (adv e A (j + 1))) := by
  classical
  obtain ⟨i, hi⟩ := A.serves (adv e A j) (advPt e A (adv e A j))
  have hne : A.conf (adv e A j) i ≠ A.conf (adv e A (j + 1)) i := by
    rw [adv_succ, hi]
    exact advPt_not_covered e A (adv e A j) i
  have hterm : dist (A.conf (adv e A j) i) (A.conf (adv e A (j + 1)) i) = 1 := hd _ _ hne
  have hsum := Finset.single_le_sum
    (f := fun i => dist (A.conf (adv e A j) i) (A.conf (adv e A (j + 1)) i))
    (fun i _ => dist_nonneg) (Finset.mem_univ i)
  simp only at hsum
  rw [hterm] at hsum
  exact hsum

/-- Against the adversary sequence of length `n`, the algorithm pays at least `n`. -/
theorem cost_adv_ge (hd : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin (k + 1) ≃ M)
    (A : OnlineAlgorithm k M) (n : ℕ) : (n : ℝ) ≤ A.cost (adv e A n) := by
  have h : ∀ j ∈ Finset.range (adv e A n).length,
      (1 : ℝ) ≤ moveCost (A.conf ((adv e A n).take j)) (A.conf ((adv e A n).take (j + 1))) := by
    intro j hj
    simp only [Finset.mem_range, adv_length] at hj
    rw [adv_take e A (le_of_lt hj), adv_take e A (by omega : j + 1 ≤ n)]
    exact one_le_step_cost hd e A j
  calc (n : ℝ) = ∑ _j ∈ Finset.range (adv e A n).length, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum h

end Adversary

section Offline

omit [MetricSpace M] in
/-- An injective configuration of `k` servers on `k+1` points avoiding `m`
covers every point other than `m`. -/
theorem covers_of_inj (e : Fin (k + 1) ≃ M) {C : Config k M} {m : M}
    (hinj : Function.Injective C) (hm : ∀ i, C i ≠ m) {p : M} (hp : p ≠ m) :
    ∃ i, C i = p := by
  have hinj' : Function.Injective (fun i => e.symm (C i)) := fun a b hab =>
    hinj (e.symm.injective hab)
  have hm' : ∀ i, e.symm (C i) ≠ e.symm m := fun i h => hm i (e.symm.injective h)
  obtain ⟨i, hi⟩ := fin_covers_of_inj hinj' hm' (p := e.symm p)
    (fun h => hp (e.symm.injective h))
  exact ⟨i, by simpa using congrArg e hi⟩

/-- The configuration of `k` servers covering every point except `m`. -/
noncomputable def complCfg (e : Fin (k + 1) ≃ M) (m : M) : Config k M := fun i =>
  e (finComplCfg (e.symm m) i)

omit [MetricSpace M] in
theorem complCfg_injective (e : Fin (k + 1) ≃ M) (m : M) :
    Function.Injective (complCfg e m) := fun _ _ hab =>
  finComplCfg_injective (e.symm m) (e.injective hab)

omit [MetricSpace M] in
theorem complCfg_ne (e : Fin (k + 1) ≃ M) (m : M) (i : Fin k) : complCfg e m i ≠ m := by
  intro h
  exact finComplCfg_ne (e.symm m) i (by simpa [complCfg] using congrArg e.symm h)

open scoped Classical in
/-- One step of the offline schedule: the configuration `C` (which misses the
point `mold`) is turned into a configuration missing `mnew`, by moving the
server sitting on `mnew` to `mold`. -/
noncomputable def stepCfg (C : Config k M) (mold mnew : M) : Config k M :=
  if h : ∃ i, C i = mnew then Function.update C h.choose mold else C

omit [MetricSpace M] in
theorem stepCfg_injective {C : Config k M} {mold mnew : M}
    (hinj : Function.Injective C) (hm : ∀ i, C i ≠ mold) :
    Function.Injective (stepCfg C mold mnew) := by
  classical
  unfold stepCfg
  split
  · rename_i h
    set i₀ := h.choose with hi₀
    intro a b hab
    by_cases ha : a = i₀ <;> by_cases hb : b = i₀
    · rw [ha, hb]
    · rw [ha] at hab ⊢
      rw [Function.update_self, Function.update_of_ne hb] at hab
      exact absurd hab.symm (hm b)
    · rw [hb] at hab ⊢
      rw [Function.update_self, Function.update_of_ne ha] at hab
      exact absurd hab (hm a)
    · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact hinj hab
  · exact hinj

omit [MetricSpace M] in
theorem stepCfg_ne {C : Config k M} {mold mnew : M}
    (hinj : Function.Injective C) (hm : ∀ i, C i ≠ mold) (i : Fin k) :
    stepCfg C mold mnew i ≠ mnew := by
  classical
  unfold stepCfg
  split
  · rename_i h
    set i₀ := h.choose with hi₀
    have hspec : C i₀ = mnew := h.choose_spec
    by_cases hi : i = i₀
    · rw [hi, Function.update_self]
      intro hcon
      exact hm i₀ (hspec.trans hcon.symm)
    · rw [Function.update_of_ne hi]
      intro hcon
      exact hi (hinj (hcon.trans hspec.symm))
  · rename_i h
    push_neg at h
    exact h i

theorem stepCfg_cost (hd : ∀ x y : M, x ≠ y → dist x y = 1) (C : Config k M) (mold mnew : M) :
    moveCost C (stepCfg C mold mnew) ≤ 1 := by
  classical
  unfold stepCfg
  split
  · rename_i h
    set i₀ := h.choose with hi₀
    have hterm : moveCost C (Function.update C i₀ mold)
        = dist (C i₀) (Function.update C i₀ mold i₀) := by
      refine Finset.sum_eq_single i₀ ?_ (by simp)
      intro b _ hb
      rw [Function.update_of_ne hb]
      simp
    rw [hterm]
    exact uniform_dist_le_one hd _ _
  · simp

omit [MetricSpace M] in
/-- In any block of `k` consecutive positions of the request sequence, at least
one of the `k+1` points is not requested. -/
theorem exists_missing (e : Fin (k + 1) ≃ M) (σ : List M) (b : ℕ) : ∃ p : M,
    ∀ j, k * b ≤ j → j < k * b + k → ∀ h : j < σ.length, σ.get ⟨j, h⟩ ≠ p := by
  classical
  obtain ⟨q, hq⟩ := fin_exists_not_mem_image (ι := Fin k) (by simp)
    (fun t : Fin k => e.symm (σ.getD (k * b + (t : ℕ)) (e 0)))
  refine ⟨e q, ?_⟩
  intro j hj1 hj2 hjlen hcon
  have ht : (j - k * b) < k := by omega
  have hjt : k * b + (j - k * b) = j := by omega
  refine hq ⟨j - k * b, ht⟩ ?_
  simp only [hjt]
  rw [List.getD_eq_getElem _ _ hjlen]
  have : σ[j] = e q := by
    rw [← hcon]
    rfl
  simp [this]

/-- A point not requested during block `b`. -/
noncomputable def miss (e : Fin (k + 1) ≃ M) (σ : List M) (b : ℕ) : M :=
  (exists_missing e σ b).choose

omit [MetricSpace M] in
theorem miss_spec (e : Fin (k + 1) ≃ M) (σ : List M) (b : ℕ) {j : ℕ} (hj1 : k * b ≤ j)
    (hj2 : j < k * b + k)
    (h : j < σ.length) : σ.get ⟨j, h⟩ ≠ miss e σ b :=
  (exists_missing e σ b).choose_spec j hj1 hj2 h

/-- The offline configuration used during block `b`. -/
noncomputable def offCfg (e : Fin (k + 1) ≃ M) (σ : List M) : ℕ → Config k M
  | 0 => complCfg e (miss e σ 0)
  | b + 1 => stepCfg (offCfg e σ b) (miss e σ b) (miss e σ (b + 1))

omit [MetricSpace M] in
theorem offCfg_inv (e : Fin (k + 1) ≃ M) (σ : List M) (b : ℕ) :
    Function.Injective (offCfg e σ b) ∧ ∀ i, offCfg e σ b i ≠ miss e σ b := by
  induction b with
  | zero => exact ⟨complCfg_injective e _, complCfg_ne e _⟩
  | succ b ih => exact ⟨stepCfg_injective ih.1 ih.2, fun i => stepCfg_ne ih.1 ih.2 i⟩

omit [MetricSpace M] in
theorem offCfg_covers (e : Fin (k + 1) ≃ M) (σ : List M) (b : ℕ) {p : M}
    (hp : p ≠ miss e σ b) : ∃ i, offCfg e σ b i = p :=
  covers_of_inj e (offCfg_inv e σ b).1 (offCfg_inv e σ b).2 hp

theorem offCfg_step_cost (e : Fin (k + 1) ≃ M) (σ : List M)
    (hd : ∀ x y : M, x ≠ y → dist x y = 1) (b : ℕ) :
    moveCost (offCfg e σ b) (offCfg e σ (b + 1)) ≤ 1 :=
  stepCfg_cost hd _ _ _

/-- The offline schedule: stay on `offCfg σ b` throughout block `b`. -/
noncomputable def offSched (e : Fin (k + 1) ≃ M) (σ : List M) (C₀ : Config k M) :
    ℕ → Config k M
  | 0 => C₀
  | j + 1 => offCfg e σ (j / k)

theorem offSched_serves (e : Fin (k + 1) ≃ M) (σ : List M) (hk : 1 ≤ k) (C₀ : Config k M) :
    ServesFrom C₀ σ (offSched e σ C₀) := by
  refine ⟨rfl, ?_⟩
  intro j
  have hj : (j : ℕ) < σ.length := j.isLt
  have hdm : k * ((j : ℕ) / k) + (j : ℕ) % k = (j : ℕ) := Nat.div_add_mod _ _
  have hmod : (j : ℕ) % k < k := Nat.mod_lt _ (by omega)
  have hne : σ.get ⟨(j : ℕ), hj⟩ ≠ miss e σ ((j : ℕ) / k) :=
    miss_spec e σ _ (by omega) (by omega) hj
  obtain ⟨i, hi⟩ := offCfg_covers e σ ((j : ℕ) / k) hne
  exact ⟨i, by simpa [offSched] using hi⟩

/-- The offline cost of any request sequence over `k+1` points is at most
`length / k + k`. -/
theorem offlineCost_le_of_uniform (e : Fin (k + 1) ≃ M) (σ : List M)
    (hd : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k)
    (C₀ : Config k M) : offlineCost C₀ σ ≤ (σ.length : ℝ) / k + k := by
  classical
  have hmain := offlineCost_le (offSched_serves e σ hk C₀)
  refine hmain.trans ?_
  rcases Nat.eq_zero_or_pos σ.length with h0 | h0
  · rw [h0]
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · obtain ⟨m, hm⟩ : ∃ m, σ.length = m + 1 := ⟨σ.length - 1, by omega⟩
    rw [hm, Finset.sum_range_succ']
    have hfirst : moveCost (offSched e σ C₀ 0) (offSched e σ C₀ (0 + 1)) ≤ (k : ℝ) := by
      simpa [offSched] using uniform_moveCost_le hd C₀ (offCfg e σ (0 / k))
    have hrest : ∀ i ∈ Finset.range m,
        moveCost (offSched e σ C₀ (i + 1)) (offSched e σ C₀ (i + 1 + 1))
          ≤ (if k ∣ (i + 1) then (1 : ℝ) else 0) := by
      intro i _
      have hdiv : (i + 1) / k = i / k + (if k ∣ (i + 1) then 1 else 0) := Nat.succ_div ..
      by_cases hdvd : k ∣ (i + 1)
      · rw [if_pos hdvd]
        have hstep : (i + 1) / k = i / k + 1 := by rw [hdiv, if_pos hdvd]
        simpa [offSched, hstep] using offCfg_step_cost e σ hd (i / k)
      · rw [if_neg hdvd]
        have hstep : (i + 1) / k = i / k := by rw [hdiv, if_neg hdvd]; omega
        simp [offSched, hstep]
    have hsum : ∑ i ∈ Finset.range m,
        moveCost (offSched e σ C₀ (i + 1)) (offSched e σ C₀ (i + 1 + 1))
        ≤ ∑ i ∈ Finset.range m, (if k ∣ (i + 1) then (1 : ℝ) else 0) :=
      Finset.sum_le_sum hrest
    have hcount : ∑ i ∈ Finset.range m, (if k ∣ (i + 1) then (1 : ℝ) else 0)
        = ((m / k : ℕ) : ℝ) := by
      rw [Finset.sum_boole, Nat.card_multiples m k]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hle : ((m / k : ℕ) : ℝ) ≤ ((m : ℝ) + 1) / (k : ℝ) := by
      refine le_trans (Nat.cast_div_le) ?_
      gcongr
      linarith
    calc ∑ i ∈ Finset.range m,
          moveCost (offSched e σ C₀ (i + 1)) (offSched e σ C₀ (i + 1 + 1))
            + moveCost (offSched e σ C₀ 0) (offSched e σ C₀ (0 + 1))
        ≤ ((m / k : ℕ) : ℝ) + (k : ℝ) :=
          add_le_add (hsum.trans (le_of_eq hcount)) hfirst
      _ ≤ ((m : ℝ) + 1) / k + k := by gcongr
      _ = ((m + 1 : ℕ) : ℝ) / k + k := by push_cast; ring

end Offline

/-- **The competitive ratio of every deterministic `k`-server algorithm on a
uniform metric space with `k+1` points is at least `k`.**  In particular the
constant `k` in the `k`-server conjecture cannot be replaced by any smaller
constant. -/
theorem uniform_not_competitive_of_lt (hk : 1 ≤ k) (e : Fin (k + 1) ≃ M)
    (hd : ∀ x y : M, x ≠ y → dist x y = 1) (A : OnlineAlgorithm k M) {c : ℝ}
    (hc : c < k) : ¬ IsCompetitive A c := by
  rintro ⟨a, ha⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have key : ∀ n : ℕ, (n : ℝ) ≤ c * offlineCost (A.conf []) (adv e A n) + a := fun n =>
    (cost_adv_ge hd e A n).trans (ha (adv e A n))
  rcases le_or_gt c 0 with hc0 | hc0
  · obtain ⟨n, hn⟩ := exists_nat_gt a
    have h1 : c * offlineCost (A.conf []) (adv e A n) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc0 (offlineCost_nonneg _ _)
    have := key n
    linarith
  · -- `c > 0`: the offline bound `n / k + k` forces `n (1 - c/k)` to stay bounded
    set t : ℝ := 1 - c / k with ht
    have htpos : 0 < t := by
      rw [ht]
      have : c / k < 1 := (div_lt_one hkpos).2 hc
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((c * k + a) / t)
    have hoff : offlineCost (A.conf []) (adv e A n) ≤ (n : ℝ) / k + k := by
      have := offlineCost_le_of_uniform e (adv e A n) hd hk (A.conf [])
      simpa using this
    have h1 : (n : ℝ) ≤ c * ((n : ℝ) / k + k) + a := by
      refine (key n).trans ?_
      have := mul_le_mul_of_nonneg_left hoff (le_of_lt hc0)
      linarith
    have h2 : (n : ℝ) * t ≤ c * k + a := by
      rw [ht]
      have : c * ((n : ℝ) / k + k) = c / k * n + c * k := by field_simp
      nlinarith [h1]
    have h3 : (c * k + a) / t < n := hn
    have h4 : c * k + a < n * t := by
      rw [div_lt_iff₀ htpos] at h3
      linarith
    linarith

end KServerLB

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (e : Fin (k + 1) ≃ M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.OnlineAlgorithm k M) (c : ℝ) (hc : c < k) :
    ¬ KServer.IsCompetitive A c :=
  KServerLB.uniform_not_competitive_of_lt hk e hd A hc
