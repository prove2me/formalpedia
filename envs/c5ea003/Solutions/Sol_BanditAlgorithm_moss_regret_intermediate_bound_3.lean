-- Prove2me | solution 3 for BanditAlgorithm.moss_regret_intermediate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T07:40:33.505083+00:00
-- url     : https://prove2.me/submissions/40671225-71bd-4a12-91ce-b1321bb5b9af

import Mathlib
import Definitions.Def_banditRegret
import Definitions.Def_mossPolicy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm.MossBuild

/-! ## M1 basics -/

lemma banditPolicy_zero_false (π : BanditPolicy 0) : False := by
  have h := (π.markov 0).isProbabilityMeasure (fun t ↦ t.elim0)
  have h1 := h.measure_univ
  have : (Set.univ : Set (Fin 0)) = ∅ := Set.univ_eq_empty_iff.mpr inferInstance
  rw [this, measure_empty] at h1
  exact zero_ne_one h1

lemma measurable_of_select_eq_dirac {k : ℕ} {π : BanditPolicy k}
    {a : (m : ℕ) → BanditHistory k m → Fin k}
    (ha : ∀ m h, π.select m h = Measure.dirac (a m h)) (m : ℕ) : Measurable (a m) := by
  refine measurable_to_countable' fun j ↦ ?_
  have : a m ⁻¹' {j} = {h | π.select m h {j} = 1} := by
    ext h
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, ha,
      Measure.dirac_apply' _ (measurableSet_singleton j)]
    by_cases hj : a m h = j
    · simp [hj]
    · simp [Set.indicator_of_notMem, hj]
  rw [this]
  exact (Kernel.measurable_coe _ (measurableSet_singleton j)) (measurableSet_singleton 1)

lemma banditArmMean_le_optimal {k : ℕ} (ν : StochasticBandit k) (i : Fin k) :
    banditArmMean ν i ≤ banditOptimalMean ν := by
  unfold banditOptimalMean
  exact le_ciSup (Set.finite_range _).bddAbove i

lemma banditGap_nonneg {k : ℕ} (ν : StochasticBandit k) (i : Fin k) : 0 ≤ banditGap ν i := by
  unfold banditGap
  linarith [banditArmMean_le_optimal ν i]

lemma exists_optimal_arm {k : ℕ} (hk : 0 < k) (ν : StochasticBandit k) :
    ∃ i, banditArmMean ν i = banditOptimalMean ν := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (banditArmMean ν)
  refine ⟨i, le_antisymm (banditArmMean_le_optimal ν i) ?_⟩
  unfold banditOptimalMean
  exact ciSup_le hi

section MossArm
variable {k n : ℕ} {π : BanditPolicy k}

/-- The (deterministic) arm MOSS plays at round `m` on history `h`. -/
noncomputable def mossArm (hπ : IsMOSSPolicy n π) (m : ℕ) (h : BanditHistory k m) : Fin k :=
  (hπ m h).choose

lemma mossArm_select (hπ : IsMOSSPolicy n π) (m : ℕ) (h : BanditHistory k m) :
    π.select m h = Measure.dirac (mossArm hπ m h) :=
  (hπ m h).choose_spec.1

lemma mossArm_unpulled (hπ : IsMOSSPolicy n π) (m : ℕ) (h : BanditHistory k m)
    (hj : ∃ j, armPullCount j h = 0) : armPullCount (mossArm hπ m h) h = 0 :=
  (hπ m h).choose_spec.2.1 hj

lemma mossArm_max (hπ : IsMOSSPolicy n π) (m : ℕ) (h : BanditHistory k m)
    (hj : ∀ j, armPullCount j h ≠ 0) (j : Fin k) :
    mossIndex n j h ≤ mossIndex n (mossArm hπ m h) h :=
  (hπ m h).choose_spec.2.2 hj j

lemma measurable_mossArm (hπ : IsMOSSPolicy n π) (m : ℕ) : Measurable (mossArm hπ m) :=
  measurable_of_select_eq_dirac (fun m h ↦ mossArm_select hπ m h) m

end MossArm

/-! ## M2 history bookkeeping -/

section History
variable {k m : ℕ}

/-- The total reward collected from arm `i` in history `h`. -/
noncomputable def armRewardSum (i : Fin k) (h : BanditHistory k m) : ℝ :=
  ∑ t ∈ {t | (h t).1 = i}.toFinset, (h t).2

lemma armEmpiricalMean_eq (i : Fin k) (h : BanditHistory k m) :
    armEmpiricalMean i h = armRewardSum i h / armPullCount i h := rfl

lemma armPullCount_eq_sum (i : Fin k) (h : BanditHistory k m) :
    armPullCount i h = ∑ t, if (h t).1 = i then 1 else 0 := by
  unfold armPullCount
  rw [Set.toFinset_setOf, Finset.card_filter]

lemma armRewardSum_eq_sum (i : Fin k) (h : BanditHistory k m) :
    armRewardSum i h = ∑ t, if (h t).1 = i then (h t).2 else 0 := by
  unfold armRewardSum
  rw [Set.toFinset_setOf, Finset.sum_filter]

lemma armPullCount_snoc (i : Fin k) (h : BanditHistory k m) (p : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h p) =
      armPullCount i h + if p.1 = i then 1 else 0 := by
  rw [armPullCount_eq_sum, armPullCount_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma armRewardSum_snoc (i : Fin k) (h : BanditHistory k m) (p : Fin k × ℝ) :
    armRewardSum i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h p) =
      armRewardSum i h + if p.1 = i then p.2 else 0 := by
  rw [armRewardSum_eq_sum, armRewardSum_eq_sum, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma armPullCount_le (i : Fin k) (h : BanditHistory k m) : armPullCount i h ≤ m := by
  unfold armPullCount
  exact (Finset.card_le_univ _).trans (by simp)

lemma sum_armPullCount (h : BanditHistory k m) : ∑ i, armPullCount i h = m := by
  simp_rw [armPullCount_eq_sum]
  rw [Finset.sum_comm]
  simp

lemma measurable_of_arms {β : Type*} [MeasurableSpace β] (g : (Fin m → Fin k) → β) :
    Measurable (fun h : BanditHistory k m ↦ g (fun t ↦ (h t).1)) := by
  have hp : Measurable (fun h : BanditHistory k m ↦ fun t ↦ (h t).1) :=
    measurable_pi_lambda _ (fun t ↦ measurable_fst.comp (measurable_pi_apply t))
  exact (measurable_of_countable g).comp hp

lemma measurable_armPullCount (i : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ armPullCount i h) := by
  have : (fun h : BanditHistory k m ↦ armPullCount i h) =
      fun h ↦ (fun v : Fin m → Fin k ↦ (Finset.univ.filter (fun t ↦ v t = i)).card)
        (fun t ↦ (h t).1) := by
    funext h
    unfold armPullCount
    rw [Set.toFinset_setOf]
  rw [this]
  exact measurable_of_arms (β := ℕ) (fun v : Fin m → Fin k ↦ (Finset.univ.filter (fun t ↦ v t = i)).card)

end History

/-! ## M3 stack space and the run map -/

abbrev Stack (k N : ℕ) := Fin k × Fin (N+1) → ℝ

noncomputable def stackMeasure {k : ℕ} (ν : StochasticBandit k) (N : ℕ) : Measure (Stack k N) :=
  Measure.pi (fun p ↦ ν.P p.1)

instance {k : ℕ} (ν : StochasticBandit k) (N : ℕ) : IsProbabilityMeasure (stackMeasure ν N) := by
  unfold stackMeasure; infer_instance

noncomputable def run {k : ℕ} (a : (m : ℕ) → BanditHistory k m → Fin k) (N : ℕ) :
    (t : ℕ) → Stack k N → BanditHistory k t
  | 0, _ => fun t ↦ t.elim0
  | t + 1, ω =>
      Fin.snoc (α := fun _ ↦ Fin k × ℝ) (run a N t ω)
        (a t (run a N t ω),
          ω (a t (run a N t ω), Fin.ofNat (N+1) (armPullCount (a t (run a N t ω)) (run a N t ω))))

section Run
variable {k N : ℕ} (a : (m : ℕ) → BanditHistory k m → Fin k)

/-- The arm played at round `t`. -/
noncomputable def runArm (t : ℕ) (ω : Stack k N) : Fin k := a t (run a N t ω)

/-- The coordinate of the stack read at round `t`. -/
noncomputable def runIdx (t : ℕ) (ω : Stack k N) : Fin k × Fin (N+1) :=
  (runArm a t ω, Fin.ofNat (N+1) (armPullCount (runArm a t ω) (run a N t ω)))

/-- The (arm, reward) pair of round `t`. -/
noncomputable def runStep (t : ℕ) (ω : Stack k N) : Fin k × ℝ :=
  (runArm a t ω, ω (runIdx a t ω))

lemma run_succ (t : ℕ) (ω : Stack k N) :
    run a N (t+1) ω = Fin.snoc (α := fun _ ↦ Fin k × ℝ) (run a N t ω) (runStep a t ω) := rfl

lemma run_pullCount_succ (i : Fin k) (t : ℕ) (ω : Stack k N) :
    armPullCount i (run a N (t+1) ω) =
      armPullCount i (run a N t ω) + if runArm a t ω = i then 1 else 0 := by
  rw [run_succ, armPullCount_snoc]
  rfl

lemma run_pullCount_mono (i : Fin k) (ω : Stack k N) {t t' : ℕ} (h : t ≤ t') :
    armPullCount i (run a N t ω) ≤ armPullCount i (run a N t' ω) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [run_pullCount_succ]; omega

lemma run_rewardSum (i : Fin k) (t : ℕ) (ω : Stack k N) :
    armRewardSum i (run a N t ω) =
      ∑ r ∈ Finset.range (armPullCount i (run a N t ω)), ω (i, Fin.ofNat (N+1) r) := by
  induction t with
  | zero =>
      have : armPullCount i (run a N 0 ω) = 0 := Nat.le_zero.mp (armPullCount_le _ _)
      rw [this, armRewardSum_eq_sum]
      simp
  | succ t ih =>
      rw [run_succ, armRewardSum_snoc, ← run_succ, run_pullCount_succ, ih]
      by_cases hi : runArm a t ω = i
      · simp only [runStep, hi, if_true, Finset.sum_range_succ, runIdx]
      · simp only [runStep, hi, if_false, add_zero]

lemma run_apply (m t : ℕ) (ht : t < m) (ω : Stack k N) :
    run a N m ω ⟨t, ht⟩ = runStep a t ω := by
  induction m with
  | zero => omega
  | succ m ih =>
      rw [run_succ]
      by_cases htm : t < m
      · have : (⟨t, ht⟩ : Fin (m+1)) = Fin.castSucc ⟨t, htm⟩ := rfl
        rw [this, Fin.snoc_castSucc, ih htm]
      · have htm' : t = m := by omega
        subst htm'
        have : (⟨t, ht⟩ : Fin (t+1)) = Fin.last t := rfl
        rw [this, Fin.snoc_last]

lemma measurable_eval_of {α : Type*} [MeasurableSpace α] {f : α → Fin k × Fin (N+1)}
    {g : α → Stack k N} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x ↦ g x (f x)) := by
  have h2 : Measurable (fun q : Stack k N × (Fin k × Fin (N+1)) ↦ q.1 q.2) :=
    measurable_from_prod_countable_left (fun p ↦ measurable_pi_apply p)
  exact h2.comp (hg.prodMk hf)

lemma measurable_run (ha : ∀ m, Measurable (a m)) (t : ℕ) :
    Measurable (run a N t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hA : Measurable (runArm a t (N := N)) := (ha t).comp ih
      have hT : Measurable (fun ω : Stack k N ↦ armPullCount (runArm a t ω) (run a N t ω)) := by
        have : Measurable (fun q : BanditHistory k t × Fin k ↦ armPullCount q.2 q.1) :=
          measurable_from_prod_countable_left (fun i ↦ measurable_armPullCount i)
        exact this.comp (ih.prodMk hA)
      have hI : Measurable (runIdx a t (N := N)) :=
        hA.prodMk ((measurable_of_countable (Fin.ofNat (N+1))).comp hT)
      have hS : Measurable (runStep a t (N := N)) :=
        hA.prodMk (measurable_eval_of hI measurable_id)
      exact measurable_banditHistorySnoc.comp (ih.prodMk hS)

/-- The run only reads coordinates `(j, r)` with `r` below the final pull count of `j`. -/
lemma run_reads_only (t : ℕ) (ω ω' : Stack k N)
    (h : ∀ (j : Fin k) (r : ℕ), r < armPullCount j (run a N t ω) →
      ω' (j, Fin.ofNat (N+1) r) = ω (j, Fin.ofNat (N+1) r)) :
    run a N t ω' = run a N t ω := by
  induction t with
  | zero => funext x; exact x.elim0
  | succ t ih =>
      have ih' : run a N t ω' = run a N t ω := by
        refine ih (fun j r hr ↦ h j r ?_)
        exact lt_of_lt_of_le hr (run_pullCount_mono a j ω (Nat.le_succ t))
      have hA : runArm a t ω' = runArm a t ω := by simp only [runArm, ih']
      rw [run_succ, run_succ, ih']
      congr 1
      simp only [runStep, runIdx, hA, ih']
      congr 1
      refine h _ _ ?_
      rw [run_pullCount_succ]
      simp

lemma run_update_of_le (t : ℕ) (ω : Stack k N) (i : Fin k) (s : Fin (N+1)) (x : ℝ)
    (hs : armPullCount i (run a N t ω) ≤ s.val) :
    run a N t (Function.update ω (i, s) x) = run a N t ω := by
  refine run_reads_only a t ω _ (fun j r hr ↦ ?_)
  rw [Function.update_of_ne]
  intro heq
  rw [Prod.mk.injEq] at heq
  obtain ⟨rfl, h2⟩ := heq
  have hrN : r < N + 1 := by have := s.isLt; omega
  have : (Fin.ofNat (N+1) r).val = r := by simp [Nat.mod_eq_of_lt hrN]
  rw [h2] at this
  omega

lemma run_update_of_le' (t : ℕ) (ω : Stack k N) (i : Fin k) (s : Fin (N+1)) (x : ℝ)
    (hs : armPullCount i (run a N t (Function.update ω (i, s) x)) ≤ s.val) :
    run a N t (Function.update ω (i, s) x) = run a N t ω := by
  have := run_update_of_le a t (Function.update ω (i, s) x) i s (ω (i, s)) hs
  rw [Function.update_idem, Function.update_eq_self] at this
  exact this.symm

lemma runIdx_eq_of_run_eq {t : ℕ} {ω ω' : Stack k N} (h : run a N t ω' = run a N t ω) :
    runIdx a t ω' = runIdx a t ω := by
  simp only [runIdx, runArm, h]

lemma runArm_eq_of_run_eq {t : ℕ} {ω ω' : Stack k N} (h : run a N t ω' = run a N t ω) :
    runArm a t ω' = runArm a t ω := by
  simp only [runArm, h]

lemma runIdx_snd_val {t : ℕ} (ht : t ≤ N) (ω : Stack k N) :
    (runIdx a t ω).2.val = armPullCount (runArm a t ω) (run a N t ω) := by
  simp only [runIdx, Fin.val_ofNat]
  have := armPullCount_le (runArm a t ω) (run a N t ω)
  exact Nat.mod_eq_of_lt (by omega)

/-- For `t ≤ N`, the run up to round `t` does not read the coordinate read at round `t`. -/
lemma run_update_runIdx {t : ℕ} (ht : t ≤ N) (ω : Stack k N) (p : Fin k × Fin (N+1)) (x : ℝ)
    (hp : runIdx a t ω = p) : run a N t (Function.update ω p x) = run a N t ω := by
  subst hp
  exact run_update_of_le a t ω (runIdx a t ω).1 (runIdx a t ω).2 x
    (le_of_eq (runIdx_snd_val a ht ω).symm)

lemma run_update_runIdx' {t : ℕ} (ht : t ≤ N) (ω : Stack k N) (p : Fin k × Fin (N+1)) (x : ℝ)
    (hp : runIdx a t (Function.update ω p x) = p) :
    run a N t (Function.update ω p x) = run a N t ω := by
  have := run_update_runIdx a ht (Function.update ω p x) p (ω p) hp
  rw [Function.update_idem, Function.update_eq_self] at this
  exact this.symm

lemma measurable_runArm (ha : ∀ m, Measurable (a m)) (t : ℕ) :
    Measurable (runArm a t (N := N)) := (ha t).comp (measurable_run a ha t)

lemma measurable_runIdx (ha : ∀ m, Measurable (a m)) (t : ℕ) :
    Measurable (runIdx a t (N := N)) := by
  have hA := measurable_runArm a ha t (N := N)
  have hT : Measurable (fun ω : Stack k N ↦ armPullCount (runArm a t ω) (run a N t ω)) := by
    have : Measurable (fun q : BanditHistory k t × Fin k ↦ armPullCount q.2 q.1) :=
      measurable_from_prod_countable_left (fun i ↦ measurable_armPullCount i)
    exact this.comp ((measurable_run a ha t).prodMk hA)
  exact hA.prodMk ((measurable_of_countable (Fin.ofNat (N+1))).comp hT)

lemma measurable_runStep (ha : ∀ m, Measurable (a m)) (t : ℕ) :
    Measurable (runStep a t (N := N)) :=
  (measurable_runArm a ha t).prodMk (measurable_eval_of (measurable_runIdx a ha t) measurable_id)

end Run

/-! ## M4 update-invariant functions are independent of that coordinate -/

section Indep
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : ι → Measure ℝ}
  [∀ i, IsProbabilityMeasure (μ i)]

lemma indepFun_of_update_invariant {β : Type*} [MeasurableSpace β] {G : (ι → ℝ) → β}
    (hG : Measurable G) (p : ι) (hinv : ∀ ω x, G (Function.update ω p x) = G ω) :
    IndepFun G (fun ω ↦ ω p) (Measure.pi μ) := by
  have hi : iIndepFun (fun q (ω : ι → ℝ) ↦ ω q) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have h2 := hi.indepFun_finset (Finset.univ.erase p) {p}
    (Finset.disjoint_singleton_right.mpr (Finset.notMem_erase p _))
    (fun q ↦ measurable_pi_apply q)
  let ext : (↥(Finset.univ.erase p) → ℝ) → (ι → ℝ) :=
    fun η q ↦ if h : q ∈ Finset.univ.erase p then η ⟨q, h⟩ else 0
  have hext : Measurable ext := by
    refine measurable_pi_lambda _ (fun q ↦ ?_)
    by_cases h : q ∈ Finset.univ.erase p
    · simp only [ext, dif_pos h]; exact measurable_pi_apply _
    · simp only [ext, dif_neg h]; exact measurable_const
  have h3 := h2.comp (hG.comp hext)
    (measurable_pi_apply (⟨p, Finset.mem_singleton_self p⟩ : ({p} : Finset ι)))
  convert h3 using 1
  funext ω
  simp only [Function.comp]
  rw [← hinv ω 0]
  congr 1
  funext q
  by_cases hq : q = p
  · subst hq; simp [ext]
  · simp [ext, hq]

omit [Fintype ι] in
lemma measurable_update_zero (p : ι) :
    Measurable (fun ω : ι → ℝ ↦ Function.update ω p 0) :=
  measurable_update'.comp (measurable_id.prodMk measurable_const)

lemma pi_inter_eval_of_invariant {E : Set (ι → ℝ)} (hE : MeasurableSet E) (p : ι)
    (hinv : ∀ ω x, Function.update ω p x ∈ E ↔ ω ∈ E) {B : Set ℝ} (hB : MeasurableSet B) :
    Measure.pi μ (E ∩ {ω | ω p ∈ B}) = Measure.pi μ E * μ p B := by
  have hind := indepFun_of_update_invariant (μ := μ) (measurable_update_zero p) p
    (fun ω x ↦ by simp [Function.update_idem])
  have h1 := hind.measure_inter_preimage_eq_mul E B hE hB
  have hEq : (fun ω : ι → ℝ ↦ Function.update ω p 0) ⁻¹' E = E := by
    ext ω; simp [hinv]
  rw [hEq] at h1
  have h2 : Measure.pi μ ((fun ω : ι → ℝ ↦ ω p) ⁻¹' B) = μ p B :=
    (measurePreserving_eval μ p).measure_preimage hB.nullMeasurableSet
  rw [h2] at h1
  exact h1

end Indep

/-! ## M5 coupling -/

section Coupling
variable {k N : ℕ} (a : (m : ℕ) → BanditHistory k m → Fin k)

lemma stack_inter_eval_of_invariant (ν : StochasticBandit k) {E : Set (Stack k N)}
    (hE : MeasurableSet E) (p : Fin k × Fin (N+1))
    (hinv : ∀ ω x, Function.update ω p x ∈ E ↔ ω ∈ E) {B : Set ℝ} (hB : MeasurableSet B) :
    stackMeasure ν N (E ∩ {ω | ω p ∈ B}) = stackMeasure ν N E * ν.P p.1 B := by
  unfold stackMeasure
  exact pi_inter_eval_of_invariant (μ := fun q : Fin k × Fin (N+1) ↦ ν.P q.1) hE p hinv hB

lemma stepKernel_apply (ν : StochasticBandit k) {π : BanditPolicy k}
    (ha : ∀ m h, π.select m h = Measure.dirac (a m h)) (t : ℕ) (h : BanditHistory k t)
    {C : Set (Fin k × ℝ)} (hC : MeasurableSet C) :
    banditStepKernel ν π t h C = ν.P (a t h) (Prod.mk (a t h) ⁻¹' C) := by
  rw [banditStepKernel, Kernel.compProd_apply hC, ha, lintegral_dirac]
  rfl

lemma compProd_map_run (ν : StochasticBandit k) {π : BanditPolicy k}
    (ha : ∀ m h, π.select m h = Measure.dirac (a m h)) {t : ℕ} (ht : t ≤ N) :
    ((stackMeasure ν N).map (run a N t)) ⊗ₘ banditStepKernel ν π t =
      (stackMeasure ν N).map (fun ω ↦ (run a N t ω, runStep a t ω)) := by
  have ham : ∀ m, Measurable (a m) := measurable_of_select_eq_dirac ha
  have hrun := measurable_run a ham t (N := N)
  have hidx := measurable_runIdx a ham t (N := N)
  set P := stackMeasure ν N with hP
  symm
  refine Measure.ext_prod (fun {S C} hS hC ↦ ?_)
  rw [Measure.compProd_apply_prod hS hC,
    Measure.map_apply (hrun.prodMk (measurable_runStep a ham t)) (hS.prod hC),
    setLIntegral_map hS (Kernel.measurable_coe _ hC) hrun]
  have hF : ∀ p, MeasurableSet (runIdx a t ⁻¹' {p} : Set (Stack k N)) :=
    fun p ↦ hidx (measurableSet_singleton p)
  -- constants
  set c : Fin k × Fin (N+1) → ENNReal := fun p ↦ ν.P p.1 (Prod.mk p.1 ⁻¹' C) with hc
  -- the LHS integrand as a finite sum of indicators
  have hint : ∀ ω, banditStepKernel ν π t (run a N t ω) C =
      ∑ p, (runIdx a t ⁻¹' {p}).indicator (fun _ ↦ c p) ω := by
    intro ω
    rw [stepKernel_apply a ν ha t _ hC]
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_ite_eq]
    simp [hc, runIdx, runArm]
  simp_rw [hint]
  rw [lintegral_finsetSum _ (fun p _ ↦ measurable_const.indicator (hF p))]
  -- the RHS measure split along runIdx
  have hsplit := sum_measure_preimage_singleton (μ := P.restrict
      ((fun ω ↦ (run a N t ω, runStep a t ω)) ⁻¹' (S ×ˢ C))) Finset.univ
      (f := runIdx a t) (fun p _ ↦ hF p)
  rw [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at hsplit
  rw [← hsplit]
  refine Finset.sum_congr rfl (fun p _ ↦ ?_)
  rw [lintegral_indicator_const (hF p), Measure.restrict_apply (hF p),
    Measure.restrict_apply (hF p)]
  -- the event E_p
  have hE : MeasurableSet (run a N t ⁻¹' S ∩ runIdx a t ⁻¹' {p}) := (hrun hS).inter (hF p)
  have hinv : ∀ ω x, Function.update ω p x ∈ run a N t ⁻¹' S ∩ runIdx a t ⁻¹' {p} ↔
      ω ∈ run a N t ⁻¹' S ∩ runIdx a t ⁻¹' {p} := by
    intro ω x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have := run_update_runIdx' a ht ω p x h2
      rw [this] at h1
      rw [runIdx_eq_of_run_eq a this] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have := run_update_runIdx a ht ω p x h2
      rw [this, runIdx_eq_of_run_eq a this]
      exact ⟨h1, h2⟩
  have hkey := stack_inter_eval_of_invariant ν hE p hinv (B := Prod.mk p.1 ⁻¹' C) (measurable_prodMk_left hC)
  have hset : runIdx a t ⁻¹' {p} ∩ (fun ω ↦ (run a N t ω, runStep a t ω)) ⁻¹' (S ×ˢ C) =
      (run a N t ⁻¹' S ∩ runIdx a t ⁻¹' {p}) ∩ {ω | ω p ∈ Prod.mk p.1 ⁻¹' C} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      subst h1
      exact ⟨⟨h2, rfl⟩, h3⟩
    · rintro ⟨⟨h2, h1⟩, h3⟩
      subst h1
      exact ⟨rfl, h2, h3⟩
  rw [hset, hkey, Set.inter_comm, mul_comm]

theorem banditMeasure_eq_map_run (ν : StochasticBandit k) {π : BanditPolicy k}
    (ha : ∀ m h, π.select m h = Measure.dirac (a m h)) :
    ∀ t ≤ N + 1, banditMeasure ν π t = (stackMeasure ν N).map (run a N t) := by
  have ham : ∀ m, Measurable (a m) := measurable_of_select_eq_dirac ha
  intro t
  induction t with
  | zero =>
      intro _
      have : run a N 0 = fun _ ↦ (fun t : Fin 0 ↦ t.elim0) := by
        funext ω x; exact x.elim0
      rw [this, Measure.map_const, measure_univ, one_smul, banditMeasure]
  | succ t ih =>
      intro ht
      rw [banditMeasure, ih (by omega), compProd_map_run a ν ha (by omega),
        Measure.map_map measurable_banditHistorySnoc
          ((measurable_run a ham t).prodMk (measurable_runStep a ham t))]
      rfl

end Coupling

/-! ## M6 regret on the stack space -/

section Regret
variable {k N : ℕ} (a : (m : ℕ) → BanditHistory k m → Fin k)

lemma runIdx_preimage_invariant {t : ℕ} (ht : t ≤ N) (p : Fin k × Fin (N+1)) (ω : Stack k N)
    (x : ℝ) : Function.update ω p x ∈ runIdx a t ⁻¹' {p} ↔ ω ∈ runIdx a t ⁻¹' {p} := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h2
    rw [runIdx_eq_of_run_eq a (run_update_runIdx' a ht ω p x h2)] at h2
    exact h2
  · intro h2
    rw [runIdx_eq_of_run_eq a (run_update_runIdx a ht ω p x h2)]
    exact h2

lemma integral_indicator_eval (ν : StochasticBandit k) (ha : ∀ m, Measurable (a m)) {t : ℕ}
    (ht : t ≤ N) (p : Fin k × Fin (N+1)) :
    ∫ ω, (runIdx a t ⁻¹' {p}).indicator (fun ω ↦ ω p) ω ∂(stackMeasure ν N) =
      (stackMeasure ν N).real (runIdx a t ⁻¹' {p}) * banditArmMean ν p.1 := by
  have hF : MeasurableSet (runIdx a t ⁻¹' {p} : Set (Stack k N)) :=
    measurable_runIdx a ha t (measurableSet_singleton p)
  set G : Stack k N → ℝ := (runIdx a t ⁻¹' {p}).indicator (fun _ ↦ (1:ℝ)) with hGdef
  have hG : Measurable G := measurable_const.indicator hF
  have hinv : ∀ ω x, G (Function.update ω p x) = G ω := by
    intro ω x
    by_cases h : ω ∈ runIdx a t ⁻¹' {p}
    · have h' := (runIdx_preimage_invariant a ht p ω x).mpr h
      simp only [G, Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : Function.update ω p x ∉ runIdx a t ⁻¹' {p} :=
        fun h'' ↦ h ((runIdx_preimage_invariant a ht p ω x).mp h'')
      simp only [G, Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hind : IndepFun G (fun ω ↦ ω p) (stackMeasure ν N) := by
    unfold stackMeasure
    exact indepFun_of_update_invariant hG p hinv
  have h1 : (fun ω ↦ (runIdx a t ⁻¹' {p}).indicator (fun ω ↦ ω p) ω) = fun ω ↦ G ω * ω p := by
    funext ω
    by_cases h : ω ∈ runIdx a t ⁻¹' {p}
    · simp only [G, Set.indicator_of_mem h, one_mul]
    · simp only [G, Set.indicator_of_notMem h, zero_mul]
  rw [h1, hind.integral_fun_mul_eq_mul_integral hG.aestronglyMeasurable
    (measurable_pi_apply p).aestronglyMeasurable]
  congr 1
  · rw [hGdef, integral_indicator_const _ hF, smul_eq_mul, mul_one]
  · unfold stackMeasure banditArmMean
    exact integral_comp_eval (μ := fun q : Fin k × Fin (N+1) ↦ ν.P q.1) (f := fun x ↦ x)
      aestronglyMeasurable_id

lemma integral_eval_runIdx (ν : StochasticBandit k) (hν : ∀ i, Integrable id (ν.P i))
    (ha : ∀ m, Measurable (a m)) {t : ℕ} (ht : t ≤ N) :
    ∫ ω, ω (runIdx a t ω) ∂(stackMeasure ν N) =
      ∫ ω, banditArmMean ν (runArm a t ω) ∂(stackMeasure ν N) := by
  have hF : ∀ p, MeasurableSet (runIdx a t ⁻¹' {p} : Set (Stack k N)) :=
    fun p ↦ measurable_runIdx a ha t (measurableSet_singleton p)
  have e1 : (fun ω : Stack k N ↦ ω (runIdx a t ω)) =
      fun ω ↦ ∑ p, (runIdx a t ⁻¹' {p}).indicator (fun ω ↦ ω p) ω := by
    funext ω
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_ite_eq]
    simp
  have e2 : (fun ω : Stack k N ↦ banditArmMean ν (runArm a t ω)) =
      fun ω ↦ ∑ p, (runIdx a t ⁻¹' {p}).indicator (fun _ ↦ banditArmMean ν p.1) ω := by
    funext ω
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_ite_eq]
    simp [runIdx]
  have hint : ∀ p : Fin k × Fin (N+1), Integrable (fun ω : Stack k N ↦ ω p) (stackMeasure ν N) := by
    intro p
    unfold stackMeasure
    exact integrable_eval (μ := fun q : Fin k × Fin (N+1) ↦ ν.P q.1) (hν p.1)
  rw [e1, e2, integral_finsetSum _ (fun p _ ↦ (hint p).indicator (hF p)),
    integral_finsetSum _ (fun p _ ↦ (integrable_const _).indicator (hF p))]
  refine Finset.sum_congr rfl (fun p _ ↦ ?_)
  rw [integral_indicator_eval a ν ha ht p, integral_indicator_const _ (hF p), smul_eq_mul]

lemma run_pullCount_eq_sum (i : Fin k) (m : ℕ) (ω : Stack k N) :
    armPullCount i (run a N m ω) = ∑ t ∈ Finset.range m, if runArm a t ω = i then 1 else 0 := by
  induction m with
  | zero => exact Nat.le_zero.mp (armPullCount_le _ _)
  | succ m ih => rw [run_pullCount_succ, ih, Finset.sum_range_succ]

lemma sum_gap_pullCount (ν : StochasticBandit k) (m : ℕ) (ω : Stack k N) :
    ∑ i, banditGap ν i * (armPullCount i (run a N m ω) : ℝ) =
      ∑ t ∈ Finset.range m, banditGap ν (runArm a t ω) := by
  simp_rw [run_pullCount_eq_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ ↦ ?_)
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem regret_eq_stack (ν : StochasticBandit k) (hν : ∀ i, Integrable id (ν.P i))
    {π : BanditPolicy k} {n : ℕ} (ha : ∀ m h, π.select m h = Measure.dirac (a m h)) :
    banditRegret ν π n =
      ∫ ω, ∑ i, banditGap ν i * (armPullCount i (run a n n ω) : ℝ) ∂(stackMeasure ν n) := by
  have ham : ∀ m, Measurable (a m) := measurable_of_select_eq_dirac ha
  have hmeasS : Measurable (fun h : BanditHistory k n ↦ ∑ t, (h t).2) :=
    Finset.measurable_sum _ (fun t _ ↦ measurable_snd.comp (measurable_pi_apply t))
  unfold banditRegret
  rw [banditMeasure_eq_map_run a ν ha n (Nat.le_succ n),
    integral_map (measurable_run a ham n).aemeasurable hmeasS.aestronglyMeasurable]
  have hX : ∀ ω : Stack k n, ∑ t, (run a n n ω t).2 =
      ∑ t ∈ Finset.range n, ω (runIdx a t ω) := by
    intro ω
    rw [Finset.sum_range (fun t ↦ ω (runIdx a t ω))]
    refine Finset.sum_congr rfl (fun t _ ↦ ?_)
    have := run_apply a n t.1 t.2 ω
    simp only [Fin.eta] at this
    rw [this]
    rfl
  simp_rw [hX, sum_gap_pullCount]
  have hF : ∀ t p, MeasurableSet (runIdx a t ⁻¹' {p} : Set (Stack k n)) :=
    fun t p ↦ measurable_runIdx a ham t (measurableSet_singleton p)
  have hintX : ∀ t, Integrable (fun ω : Stack k n ↦ ω (runIdx a t ω)) (stackMeasure ν n) := by
    intro t
    have e1 : (fun ω : Stack k n ↦ ω (runIdx a t ω)) =
        fun ω ↦ ∑ p, (runIdx a t ⁻¹' {p}).indicator (fun ω ↦ ω p) ω := by
      funext ω
      simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
      rw [Finset.sum_ite_eq]
      simp
    rw [e1]
    refine integrable_finsetSum _ (fun p _ ↦ ?_)
    have : Integrable (fun ω : Stack k n ↦ ω p) (stackMeasure ν n) := by
      unfold stackMeasure
      exact integrable_eval (μ := fun q : Fin k × Fin (n+1) ↦ ν.P q.1) (hν p.1)
    exact this.indicator (hF t p)
  have hintA : ∀ (f : Fin k → ℝ) t, Integrable (fun ω : Stack k n ↦ f (runArm a t ω))
      (stackMeasure ν n) := by
    intro f t
    have e2 : (fun ω : Stack k n ↦ f (runArm a t ω)) =
        fun ω ↦ ∑ p, (runIdx a t ⁻¹' {p}).indicator (fun _ ↦ f p.1) ω := by
      funext ω
      simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
      rw [Finset.sum_ite_eq]
      simp [runIdx]
    rw [e2]
    exact integrable_finsetSum _ (fun p _ ↦ (integrable_const _).indicator (hF t p))
  rw [integral_finsetSum _ (fun t _ ↦ hintX t), integral_finsetSum _ (fun t _ ↦ hintA _ t)]
  have hΔ : ∀ t ∈ Finset.range n, ∫ ω, banditGap ν (runArm a t ω) ∂(stackMeasure ν n) =
      banditOptimalMean ν - ∫ ω, ω (runIdx a t ω) ∂(stackMeasure ν n) := by
    intro t ht
    rw [integral_eval_runIdx a ν hν ham (by simp at ht; omega)]
    simp only [banditGap]
    rw [integral_sub (integrable_const _) (hintA _ t), integral_const, probReal_univ,
      one_smul]
  rw [Finset.sum_congr rfl hΔ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

end Regret

/-! ## M7 pathwise MOSS inequality -/

section Pathwise
variable {k n : ℕ}

/-- The MOSS index of arm `i` after `s` pulls, read off the reward stack. -/
noncomputable def U (ω : Stack k n) (i : Fin k) (s : ℕ) : ℝ :=
  (∑ r ∈ Finset.range s, ω (i, Fin.ofNat (n+1) r)) / (s : ℝ) +
    Real.sqrt ((4 / (s : ℝ)) * logPlus ((n : ℝ) / ((k : ℝ) * (s : ℝ))))

/-- Number of pull counts `s ∈ [1, n)` at which arm `i`'s index is at least `lvl`. -/
noncomputable def kappa (ω : Stack k n) (i : Fin k) (lvl : ℝ) : ℕ :=
  ((Finset.Ico 1 n).filter (fun s ↦ lvl ≤ U ω i s)).card

/-- The largest underestimate of `μs` by arm `i₀`'s index over `s ∈ [1, n)`, floored at `0`. -/
noncomputable def Zmax (ω : Stack k n) (i₀ : Fin k) (μs : ℝ) : ℝ :=
  (Finset.Ico 1 n).fold max 0 (fun s ↦ μs - U ω i₀ s)

lemma Zmax_nonneg (ω : Stack k n) (i₀ : Fin k) (μs : ℝ) : 0 ≤ Zmax ω i₀ μs :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)

lemma le_Zmax (ω : Stack k n) (i₀ : Fin k) (μs : ℝ) {s : ℕ} (hs : s ∈ Finset.Ico 1 n) :
    μs - U ω i₀ s ≤ Zmax ω i₀ μs :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨s, hs, le_rfl⟩)

lemma mossIndex_run (a : (m : ℕ) → BanditHistory k m → Fin k) (t : ℕ) (ω : Stack k n)
    (i : Fin k) : mossIndex n i (run a n t ω) = U ω i (armPullCount i (run a n t ω)) := by
  unfold mossIndex U
  rw [armEmpiricalMean_eq, run_rewardSum]

theorem pathwise {π : BanditPolicy k} (hπ : IsMOSSPolicy n π) (ν : StochasticBandit k)
    (i₀ : Fin k) (D : ℝ) (hD : 0 ≤ D) (ω : Stack k n) :
    ∑ i, banditGap ν i * (armPullCount i (run (mossArm hπ) n n ω) : ℝ) ≤
      n * (D + 2 * max 0 (Zmax ω i₀ (banditOptimalMean ν) - D / 2)) +
      ∑ i ∈ Finset.univ.filter (fun i ↦ D < banditGap ν i),
        banditGap ν i * (1 + (kappa ω i (banditOptimalMean ν - banditGap ν i / 2) : ℝ)) := by
  classical
  set μs := banditOptimalMean ν with hμs
  set B := D + 2 * max 0 (Zmax ω i₀ μs - D / 2) with hB
  set L := Finset.univ.filter (fun i ↦ D < banditGap ν i) with hL
  let T : ℕ → Fin k → ℕ := fun t i ↦ armPullCount i (run (mossArm hπ) n t ω)
  let A : ℕ → Fin k := fun t ↦ runArm (mossArm hπ) t ω
  let bad : ℕ → Prop := fun t ↦
    A t ∈ L ∧ (T t (A t) = 0 ∨ μs - banditGap ν (A t) / 2 ≤ U ω (A t) (T t (A t)))
  rw [sum_gap_pullCount, ← Finset.sum_filter_add_sum_filter_not (Finset.range n) bad]
  have hB0 : 0 ≤ B := by
    have : 0 ≤ max 0 (Zmax ω i₀ μs - D / 2) := le_max_left _ _
    linarith
  have hDB : D ≤ B := by
    have : 0 ≤ max 0 (Zmax ω i₀ μs - D / 2) := le_max_left _ _
    linarith
  -- rounds that are not charged to an arm
  have hgood : ∀ t ∈ (Finset.range n).filter (fun t ↦ ¬ bad t),
      banditGap ν (runArm (mossArm hπ) t ω) ≤ B := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htn, hnb⟩ := ht
    by_cases hAL : A t ∈ L
    · have hnb' : T t (A t) ≠ 0 ∧ U ω (A t) (T t (A t)) < μs - banditGap ν (A t) / 2 := by
        simp only [bad, not_and, not_or, not_le] at hnb
        exact hnb hAL
      obtain ⟨hT0, hU⟩ := hnb'
      -- all arms have been pulled
      have hall : ∀ j, armPullCount j (run (mossArm hπ) n t ω) ≠ 0 := by
        intro j hj
        exact hT0 (mossArm_unpulled hπ t _ ⟨j, hj⟩)
      have hmax := mossArm_max hπ t (run (mossArm hπ) n t ω) hall i₀
      rw [mossIndex_run, mossIndex_run] at hmax
      have hi₀mem : armPullCount i₀ (run (mossArm hπ) n t ω) ∈ Finset.Ico 1 n := by
        rw [Finset.mem_Ico]
        exact ⟨Nat.pos_of_ne_zero (hall i₀), lt_of_le_of_lt (armPullCount_le _ _) htn⟩
      have hZ := le_Zmax ω i₀ μs hi₀mem
      have hlt : banditGap ν (A t) < 2 * Zmax ω i₀ μs := by
        have : U ω (A t) (T t (A t)) =
            U ω (mossArm hπ t (run (mossArm hπ) n t ω))
              (armPullCount (mossArm hπ t (run (mossArm hπ) n t ω)) (run (mossArm hπ) n t ω)) :=
          rfl
        rw [this] at hU
        linarith
      have : Zmax ω i₀ μs - D / 2 ≤ max 0 (Zmax ω i₀ μs - D / 2) := le_max_right _ _
      show banditGap ν (A t) ≤ B
      linarith
    · have : ¬ D < banditGap ν (A t) := by
        intro h; exact hAL (by simp [hL, h])
      show banditGap ν (A t) ≤ B
      linarith [not_lt.mp this]
  have h1 : ∑ t ∈ (Finset.range n).filter (fun t ↦ ¬ bad t), banditGap ν (runArm (mossArm hπ) t ω)
      ≤ n * B := by
    calc ∑ t ∈ (Finset.range n).filter (fun t ↦ ¬ bad t), banditGap ν (runArm (mossArm hπ) t ω)
        ≤ ∑ t ∈ (Finset.range n).filter (fun t ↦ ¬ bad t), B := Finset.sum_le_sum hgood
      _ = ((Finset.range n).filter (fun t ↦ ¬ bad t)).card * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * B := by
          refine mul_le_mul_of_nonneg_right ?_ hB0
          have := (Finset.card_filter_le (Finset.range n) (fun t ↦ ¬ bad t)).trans
            (Finset.card_range n).le
          exact_mod_cast this
  -- rounds charged to arm `i ∈ L`
  have hcard : ∀ i ∈ L, ((((Finset.range n).filter bad).filter (fun t ↦ A t = i)).card : ℝ) ≤
      1 + (kappa ω i (μs - banditGap ν i / 2) : ℝ) := by
    intro i _
    have hle : (((Finset.range n).filter bad).filter (fun t ↦ A t = i)).card ≤
        (insert 0 ((Finset.Ico 1 n).filter (fun s ↦ μs - banditGap ν i / 2 ≤ U ω i s))).card := by
      refine Finset.card_le_card_of_injOn (fun t ↦ T t i) ?_ ?_
      · intro t ht
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at ht
        obtain ⟨⟨htn, _, hb⟩, hAi⟩ := ht
        rw [hAi] at hb
        simp only [Finset.coe_insert, Finset.coe_filter, Finset.mem_Ico, Set.mem_insert_iff,
          Set.mem_setOf_eq]
        rcases hb with hb | hb
        · exact Or.inl hb
        · by_cases h0 : T t i = 0
          · exact Or.inl h0
          · exact Or.inr ⟨⟨Nat.pos_of_ne_zero h0,
              lt_of_le_of_lt (armPullCount_le _ _) htn⟩, hb⟩
      · intro t₁ ht₁ t₂ ht₂ heq
        rw [Finset.mem_coe, Finset.mem_filter] at ht₁ ht₂
        have hA₁ : runArm (mossArm hπ) t₁ ω = i := ht₁.2
        have hA₂ : runArm (mossArm hπ) t₂ ω = i := ht₂.2
        have heq' : armPullCount i (run (mossArm hπ) n t₁ ω) =
            armPullCount i (run (mossArm hπ) n t₂ ω) := heq
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have h1 := run_pullCount_mono (mossArm hπ) i ω (Nat.succ_le_of_lt hlt)
          rw [run_pullCount_succ, if_pos hA₁] at h1
          omega
        · have h1 := run_pullCount_mono (mossArm hπ) i ω (Nat.succ_le_of_lt hlt)
          rw [run_pullCount_succ, if_pos hA₂] at h1
          omega
    have h2 := hle.trans (Finset.card_insert_le _ _)
    unfold kappa
    have h3 : ((((Finset.range n).filter bad).filter (fun t ↦ A t = i)).card : ℝ) ≤
        (((Finset.Ico 1 n).filter (fun s ↦ μs - banditGap ν i / 2 ≤ U ω i s)).card : ℝ) + 1 := by
      exact_mod_cast h2
    linarith
  have h2 : ∑ t ∈ (Finset.range n).filter bad, banditGap ν (runArm (mossArm hπ) t ω) ≤
      ∑ i ∈ L, banditGap ν i * (1 + (kappa ω i (μs - banditGap ν i / 2) : ℝ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := A) (t := L)
      (fun t ht ↦ (Finset.mem_filter.mp ht).2.1)]
    refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [Finset.sum_congr rfl (fun t ht ↦ by
      rw [show runArm (mossArm hπ) t ω = i from (Finset.mem_filter.mp ht).2])]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hcard i hi) (banditGap_nonneg ν i)
  linarith

end Pathwise

/-! ## M8 stack Hoeffding -/

section StackHoeffding
variable {k N : ℕ}

lemma stack_iIndep (ν : StochasticBandit k) :
    iIndepFun (fun (p : Fin k × Fin (N+1)) (ω : Stack k N) ↦ ω p - banditArmMean ν p.1)
      (stackMeasure ν N) := by
  unfold stackMeasure
  exact iIndepFun_pi (X := fun (p : Fin k × Fin (N+1)) (x : ℝ) ↦ x - banditArmMean ν p.1)
    (fun p ↦ (measurable_id.sub_const _).aemeasurable)

lemma stack_map_eval (ν : StochasticBandit k) (p : Fin k × Fin (N+1)) :
    (stackMeasure ν N).map (fun ω ↦ ω p) = ν.P p.1 := by
  unfold stackMeasure
  exact (measurePreserving_eval (fun q : Fin k × Fin (N+1) ↦ ν.P q.1) p).map_eq

lemma stack_subG (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (p : Fin k × Fin (N+1)) :
    HasSubgaussianMGF (fun ω : Stack k N ↦ ω p - banditArmMean ν p.1) 1 (stackMeasure ν N) := by
  have h := hν.2 p.1
  rw [one_pow, ← stack_map_eval ν p (N := N)] at h
  have h2 := HasSubgaussianMGF.of_map (μ := stackMeasure ν N) (Y := fun ω : Stack k N ↦ ω p)
    (measurable_pi_apply p).aemeasurable h
  exact h2

lemma stack_hoeffding (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν) (i : Fin k)
    {s : ℕ} (hs : s ≤ N + 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (stackMeasure ν N).real
      {ω | ε ≤ ∑ r ∈ Finset.range s, (ω (i, Fin.ofNat (N+1) r) - banditArmMean ν i)} ≤
      Real.exp (-ε ^ 2 / (2 * s)) := by
  set g : ℕ → Fin k × Fin (N+1) := fun r ↦ (i, Fin.ofNat (N+1) r) with hg
  have hinj : Set.InjOn g (Finset.range s : Set ℕ) := by
    intro r₁ h₁ r₂ h₂ heq
    simp only [Finset.coe_range, Set.mem_Iio] at h₁ h₂
    simp only [hg, Prod.mk.injEq, true_and] at heq
    have := congrArg Fin.val heq
    simp only [Fin.val_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hsum : ∀ ω : Stack k N, ∑ r ∈ Finset.range s, (ω (i, Fin.ofNat (N+1) r) - banditArmMean ν i)
      = ∑ p ∈ (Finset.range s).image g, (ω p - banditArmMean ν p.1) := by
    intro ω
    rw [Finset.sum_image (fun x hx y hy h ↦ hinj hx hy h)]
  simp_rw [hsum]
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (stack_iIndep ν (N := N))
    (c := fun _ ↦ 1) (s := (Finset.range s).image g) (fun p _ ↦ stack_subG ν hν p) hε
  convert h using 3
  rw [Finset.sum_const, Finset.card_image_of_injOn hinj, Finset.card_range]
  simp

end StackHoeffding

/-! ## M9 the κ bound -/

section Kappa
variable {k n : ℕ}

lemma measurable_U (i : Fin k) (s : ℕ) : Measurable (fun ω : Stack k n ↦ U ω i s) := by
  unfold U
  refine Measurable.add_const (Measurable.div_const ?_ _) _
  exact Finset.measurable_sum _ (fun r _ ↦ measurable_pi_apply _)

lemma kappa_eq_sum (ω : Stack k n) (i : Fin k) (lvl : ℝ) :
    (kappa ω i lvl : ℝ) =
      ∑ s ∈ Finset.Ico 1 n, {ω : Stack k n | lvl ≤ U ω i s}.indicator (fun _ ↦ (1:ℝ)) ω := by
  unfold kappa
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun s _ ↦ ?_)
  by_cases h : lvl ≤ U ω i s
  · simp [h]
  · simp [h]

lemma integral_kappa (ν : StochasticBandit k) (i : Fin k) (lvl : ℝ) :
    ∫ ω, (kappa ω i lvl : ℝ) ∂(stackMeasure ν n) =
      ∑ s ∈ Finset.Ico 1 n, (stackMeasure ν n).real {ω : Stack k n | lvl ≤ U ω i s} := by
  have hm : ∀ s, MeasurableSet {ω : Stack k n | lvl ≤ U ω i s} :=
    fun s ↦ measurableSet_le measurable_const (measurable_U i s)
  simp_rw [kappa_eq_sum]
  rw [integral_finsetSum _ (fun s _ ↦ (integrable_const _).indicator (hm s))]
  refine Finset.sum_congr rfl (fun s _ ↦ ?_)
  rw [integral_indicator_const _ (hm s), smul_eq_mul, mul_one]

lemma logPlus_le_max (x : ℝ) : logPlus x ≤ max 1 (Real.log x) := by
  unfold logPlus
  by_cases hx : 1 ≤ x
  · rw [max_eq_right hx]; exact le_max_right _ _
  · rw [max_eq_left (le_of_lt (not_le.mp hx)), Real.log_one]
    exact le_trans zero_le_one (le_max_left _ _)

lemma two_log_le (z : ℝ) (hz : 0 < z) : 2 * Real.log z ≤ z := by
  have h1 : Real.log z = 2 * Real.log (Real.sqrt z) := by
    rw [Real.log_sqrt hz.le]; ring
  have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hz)
  have h3 := Real.sq_sqrt hz.le
  nlinarith [sq_nonneg (Real.sqrt z - 2)]

lemma geom_exp_sum_le (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ∑ s ∈ Finset.Ico 1 n, Real.exp (-(s : ℝ) * c) ≤ 1 / c := by
  set q := Real.exp (-c) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have := Real.exp_lt_exp.mpr (show -c < 0 by linarith)
    rwa [Real.exp_zero] at this
  have e : ∀ s : ℕ, Real.exp (-(s : ℝ) * c) = q ^ s := by
    intro s
    rw [hq, ← Real.exp_nat_mul]
    ring_nf
  simp_rw [e]
  refine (geom_sum_Ico_le_of_lt_one hq0 hq1).trans ?_
  rw [pow_one, div_le_div_iff₀ (by linarith) hc]
  have h1 := Real.add_one_le_exp c
  have h2 : q * Real.exp c = 1 := by rw [hq, ← Real.exp_add]; simp
  nlinarith

theorem kappa_integral_le (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν) (hk : 0 < k)
    (hkn : k ≤ n) (i : Fin k) (hΔ : 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i) :
    banditGap ν i * ∫ ω, (kappa ω i (banditOptimalMean ν - banditGap ν i / 2) : ℝ)
      ∂(stackMeasure ν n) ≤ 12 * Real.sqrt ((n : ℝ) / k) := by
  set Δ := banditGap ν i with hΔdef
  set r := Real.sqrt ((n : ℝ) / k) with hr
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hkn)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (div_pos hnR hkR)
  have hr2 : r ^ 2 = (n : ℝ) / k := Real.sq_sqrt (div_pos hnR hkR).le
  have hinv : Real.sqrt ((k : ℝ) / n) = r⁻¹ := by
    rw [hr, ← Real.sqrt_inv, inv_div]
  rw [hinv] at hΔ
  have hΔ0 : 0 < Δ := lt_trans (by positivity) hΔ
  have hΔr : 8 < Δ * r := by
    have := mul_lt_mul_of_pos_right hΔ hr0
    rwa [mul_assoc, inv_mul_cancel₀ hr0.ne', mul_one] at this
  set L₀ := max 1 (Real.log ((n : ℝ) * Δ ^ 2 / (64 * k))) with hL₀
  set s₀ := 64 * L₀ / Δ ^ 2 with hs₀
  set c := Δ ^ 2 / 32 with hc
  have hc0 : 0 < c := by positivity
  have hL₁ : 1 ≤ L₀ := le_max_left _ _
  have hs₀0 : 0 ≤ s₀ := by positivity
  set lvl := banditOptimalMean ν - Δ / 2 with hlvl
  have hlvl' : lvl = banditArmMean ν i + Δ / 2 := by
    rw [hlvl, hΔdef, banditGap]; ring
  -- per-s bound
  have hper : ∀ s ∈ Finset.Ico 1 n, (stackMeasure ν n).real {ω : Stack k n | lvl ≤ U ω i s} ≤
      (if (s : ℝ) < s₀ then 1 else 0) + Real.exp (-(s : ℝ) * c) := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs.1
    have hs0 : (0 : ℝ) < s := by linarith
    by_cases hss : (s : ℝ) < s₀
    · rw [if_pos hss]
      have := measureReal_le_one (μ := stackMeasure ν n) (s := {ω : Stack k n | lvl ≤ U ω i s})
      linarith [Real.exp_pos (-(s : ℝ) * c)]
    · rw [if_neg hss, zero_add]
      have hss' : s₀ ≤ s := not_lt.mp hss
      -- the bonus is at most Δ/4
      have hsΔ : 64 * L₀ ≤ s * Δ ^ 2 := by
        rw [hs₀, div_le_iff₀ (by positivity)] at hss'
        linarith
      have h64 : 64 ≤ (s : ℝ) * Δ ^ 2 := by linarith
      have hbonus : Real.sqrt ((4 / (s : ℝ)) * logPlus ((n : ℝ) / ((k : ℝ) * (s : ℝ)))) ≤ Δ / 4 := by
        have hlog : logPlus ((n : ℝ) / ((k : ℝ) * (s : ℝ))) ≤ L₀ := by
          refine (logPlus_le_max _).trans ?_
          rw [hL₀]
          refine max_le_max le_rfl (Real.log_le_log (by positivity) ?_)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : (n : ℝ) * (64 * k) ≤ n * Δ ^ 2 * (k * s) := by
            have := mul_le_mul_of_nonneg_left h64 (le_of_lt (mul_pos hnR hkR))
            nlinarith
          linarith
        have h1 : (4 / (s : ℝ)) * logPlus ((n : ℝ) / ((k : ℝ) * (s : ℝ))) ≤ (Δ / 4) ^ 2 := by
          calc (4 / (s : ℝ)) * logPlus ((n : ℝ) / ((k : ℝ) * (s : ℝ)))
              ≤ (4 / (s : ℝ)) * L₀ := mul_le_mul_of_nonneg_left hlog (by positivity)
            _ ≤ (Δ / 4) ^ 2 := by
              rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
              nlinarith
        calc Real.sqrt ((4 / (s : ℝ)) * logPlus ((n : ℝ) / ((k : ℝ) * (s : ℝ))))
            ≤ Real.sqrt ((Δ / 4) ^ 2) := Real.sqrt_le_sqrt h1
          _ = Δ / 4 := Real.sqrt_sq (by positivity)
      have hsub : {ω : Stack k n | lvl ≤ U ω i s} ⊆
          {ω | (s : ℝ) * Δ / 4 ≤
            ∑ r ∈ Finset.range s, (ω (i, Fin.ofNat (n+1) r) - banditArmMean ν i)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        unfold U at hω
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        set S := ∑ r ∈ Finset.range s, ω (i, Fin.ofNat (n+1) r)
        have h2 : banditArmMean ν i + Δ / 4 ≤ S / s := by linarith
        rw [le_div_iff₀ hs0] at h2
        linarith
      refine (measureReal_mono hsub).trans ?_
      refine (stack_hoeffding ν hν i (by omega) (by positivity)).trans (le_of_eq ?_)
      congr 1
      rw [hc]
      field_simp
      ring
  -- sum up
  rw [integral_kappa]
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_boole] at hsum
  have hcard : ((Finset.Ico 1 n).filter (fun s : ℕ ↦ (s : ℝ) < s₀)).card ≤ s₀ := by
    have hsub : (Finset.Ico 1 n).filter (fun s : ℕ ↦ (s : ℝ) < s₀) ⊆ Finset.Icc 1 ⌊s₀⌋₊ := by
      intro s hs
      rw [Finset.mem_filter, Finset.mem_Ico] at hs
      rw [Finset.mem_Icc]
      exact ⟨hs.1.1, Nat.le_floor hs.2.le⟩
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    calc (((Finset.Ico 1 n).filter (fun s : ℕ ↦ (s : ℝ) < s₀)).card : ℝ)
        ≤ (⌊s₀⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ s₀ := Nat.floor_le hs₀0
  have hgeom := geom_exp_sum_le c hc0 n
  have htot : ∑ s ∈ Finset.Ico 1 n, (stackMeasure ν n).real {ω : Stack k n | lvl ≤ U ω i s} ≤
      s₀ + 1 / c := by linarith
  -- arithmetic
  have hz : (n : ℝ) * Δ ^ 2 / (64 * k) = (Δ * r / 8) ^ 2 := by
    rw [div_pow, mul_pow, hr2]
    field_simp
    ring
  have hL₀le : 8 * L₀ ≤ Δ * r := by
    rw [hL₀, hz, Real.log_pow]
    have := two_log_le (Δ * r / 8) (by positivity)
    rcases le_total 1 (((2 : ℕ) : ℝ) * Real.log (Δ * r / 8)) with h | h
    · rw [max_eq_right h]; push_cast at this ⊢; linarith
    · rw [max_eq_left h]; linarith
  have hA : Δ * s₀ ≤ 8 * r := by
    rw [hs₀, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hB : Δ * (1 / c) ≤ 4 * r := by
    rw [hc, one_div_div, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  calc Δ * ∑ s ∈ Finset.Ico 1 n, (stackMeasure ν n).real {ω : Stack k n | lvl ≤ U ω i s}
      ≤ Δ * (s₀ + 1 / c) := mul_le_mul_of_nonneg_left htot hΔ0.le
    _ ≤ 12 * r := by linarith

end Kappa

/-! ## M10 maximal Hoeffding inequality (first passage) -/

section Maximal
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}

/-- Partial sums `∑_{j < s} v j` of a finite vector. -/
noncomputable def psum (v : Fin m → ℝ) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin m ↦ (j : ℕ) < s), v j

lemma measurable_psum (s : ℕ) : Measurable (fun v : Fin m → ℝ ↦ psum v s) :=
  Finset.measurable_sum _ (fun j _ ↦ measurable_pi_apply j)

lemma psum_all (v : Fin m → ℝ) : psum v m = ∑ j, v j := by
  unfold psum
  rw [Finset.filter_true_of_mem (fun j _ ↦ j.isLt)]

/-- The coordinates below `s` (others zeroed). -/
def lowPart (s : ℕ) (v : Fin m → ℝ) : Fin m → ℝ := fun j ↦ if (j : ℕ) < s then v j else 0

/-- The coordinates at or above `s` (others zeroed). -/
def highPart (s : ℕ) (v : Fin m → ℝ) : Fin m → ℝ := fun j ↦ if (j : ℕ) < s then 0 else v j

lemma psum_lowPart {r s : ℕ} (h : r ≤ s) (v : Fin m → ℝ) : psum (lowPart s v) r = psum v r := by
  unfold psum lowPart
  refine Finset.sum_congr rfl (fun j hj ↦ ?_)
  rw [Finset.mem_filter] at hj
  rw [if_pos (by omega)]

lemma sum_highPart (s : ℕ) (v : Fin m → ℝ) : ∑ j, highPart s v j = psum v m - psum v s := by
  rw [psum_all]
  unfold psum highPart
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin m ↦ (j : ℕ) < s)]
  ring

lemma measurableSet_firstPassage {X : Type*} [MeasurableSpace X] {f : ℕ → X → ℝ}
    (hf : ∀ r, Measurable (f r)) (a : ℝ) (s : ℕ) :
    MeasurableSet {x | a ≤ f s x ∧ ∀ r ∈ Finset.range s, f r x < a} := by
  have : {x | a ≤ f s x ∧ ∀ r ∈ Finset.range s, f r x < a} =
      {x | a ≤ f s x} ∩ ⋂ r ∈ Finset.range s, {x | f r x < a} := by
    ext x; simp
  rw [this]
  exact (measurableSet_le measurable_const (hf s)).inter
    (Finset.measurableSet_biInter _ (fun r _ ↦ measurableSet_lt (hf r) measurable_const))

omit [IsProbabilityMeasure P] in
lemma indep_low_high {Y : Fin m → Ω → ℝ} (hmeas : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P)
    (s : ℕ) :
    IndepFun (fun ω ↦ lowPart s (fun j ↦ Y j ω)) (fun ω ↦ highPart s (fun j ↦ Y j ω)) P := by
  classical
  set S := Finset.univ.filter (fun j : Fin m ↦ (j : ℕ) < s) with hS
  set T := Finset.univ.filter (fun j : Fin m ↦ ¬ (j : ℕ) < s) with hT
  have hST : Disjoint S T := Finset.disjoint_filter_filter_not _ _ _
  have h2 := hind.indepFun_finset S T hST hmeas
  let φ : (↥S → ℝ) → (Fin m → ℝ) := fun w j ↦ if h : j ∈ S then w ⟨j, h⟩ else 0
  let ψ : (↥T → ℝ) → (Fin m → ℝ) := fun w j ↦ if h : j ∈ T then w ⟨j, h⟩ else 0
  have hφ : Measurable φ := by
    refine measurable_pi_lambda _ (fun j ↦ ?_)
    by_cases h : j ∈ S
    · simp only [φ, dif_pos h]; exact measurable_pi_apply _
    · simp only [φ, dif_neg h]; exact measurable_const
  have hψ : Measurable ψ := by
    refine measurable_pi_lambda _ (fun j ↦ ?_)
    by_cases h : j ∈ T
    · simp only [ψ, dif_pos h]; exact measurable_pi_apply _
    · simp only [ψ, dif_neg h]; exact measurable_const
  have h3 := h2.comp hφ hψ
  convert h3 using 1
  · funext ω j
    by_cases h : (j : ℕ) < s
    · have hj : j ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      simp [φ, lowPart, h, hj]
    · have hj : j ∉ S := by rw [hS, Finset.mem_filter]; exact fun h' ↦ h h'.2
      simp [φ, lowPart, h, hj]
  · funext ω j
    by_cases h : (j : ℕ) < s
    · have hj : j ∉ T := by rw [hT, Finset.mem_filter]; exact fun h' ↦ h'.2 h
      simp [ψ, highPart, h, hj]
    · have hj : j ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      simp [ψ, highPart, h, hj]

theorem maximal_hoeffding {Y : Fin m → Ω → ℝ} (hmeas : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y P) (hsub : ∀ j, HasSubgaussianMGF (Y j) 1 P)
    (hmean : ∀ j, ∫ ω, Y j ω ∂P = 0) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ s ≤ m, a ≤ psum (fun j ↦ Y j ω) s} ≤ Real.exp (-a ^ 2 / (2 * m)) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have : {ω | ∃ s ≤ 0, a ≤ psum (fun j ↦ Y j ω) s} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro s _ hs
      unfold psum at hs
      simp at hs
      linarith
    rw [this, measureReal_empty]
    exact (Real.exp_pos _).le
  set S : ℕ → Ω → ℝ := fun s ω ↦ psum (fun j ↦ Y j ω) s with hSdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set l := a / m with hl
  have hl0 : 0 < l := div_pos ha hmR
  have hSmeas : ∀ s, Measurable (S s) :=
    fun s ↦ (measurable_psum s).comp (measurable_pi_lambda _ hmeas)
  set E : ℕ → Set Ω := fun s ↦ {ω | a ≤ S s ω ∧ ∀ r ∈ Finset.range s, S r ω < a} with hE
  have hEmeas : ∀ s, MeasurableSet (E s) := fun s ↦ measurableSet_firstPassage hSmeas a s
  have hunion : {ω | ∃ s ≤ m, a ≤ psum (fun j ↦ Y j ω) s} = ⋃ s ∈ Finset.range (m+1), E s := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop, hE]
    constructor
    · intro h
      have h' : ∃ s, s ≤ m ∧ a ≤ S s ω := h
      have hspec := Nat.find_spec h'
      refine ⟨Nat.find h', by omega, hspec.2, fun r hr ↦ ?_⟩
      have hmin := Nat.find_min h' hr
      simp only [not_and, not_le] at hmin
      exact hmin (by omega)
    · rintro ⟨s, hs, h1, _⟩
      exact ⟨s, by omega, h1⟩
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (m+1))) E := by
    intro s _ s' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd h1.1 (not_le.mpr (h2.2 s (Finset.mem_range.mpr h)))
    · exact absurd h2.1 (not_le.mpr (h1.2 s' (Finset.mem_range.mpr h)))
  have hsubU : ∀ U : Finset (Fin m),
      HasSubgaussianMGF (fun ω ↦ ∑ j ∈ U, Y j ω) (∑ j ∈ U, (1 : ℝ≥0)) P :=
    fun U ↦ HasSubgaussianMGF.sum_of_iIndepFun hind (fun j _ ↦ hsub j)
  have hexpS : ∀ s, Integrable (fun ω ↦ Real.exp (l * S s ω)) P :=
    fun s ↦ (hsubU (Finset.univ.filter (fun j : Fin m ↦ (j : ℕ) < s))).integrable_exp_mul l
  -- the per-`s` bound
  have hper : ∀ s ∈ Finset.range (m+1),
      Real.exp (l * a) * P.real (E s) ≤ ∫ ω in E s, Real.exp (l * S m ω) ∂P := by
    intro s _
    set F : Ω → ℝ := (E s).indicator (fun ω ↦ Real.exp (l * S s ω)) with hF
    set G : Ω → ℝ := fun ω ↦ Real.exp (l * (S m ω - S s ω)) with hG
    -- (1)
    have h1 : Real.exp (l * a) * P.real (E s) ≤ ∫ ω, F ω ∂P := by
      rw [hF, integral_indicator (hEmeas s), mul_comm, ← smul_eq_mul, ← setIntegral_const]
      refine setIntegral_mono_on (integrableOn_const) (hexpS s).integrableOn (hEmeas s)
        (fun ω hω ↦ ?_)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω.1 hl0.le)
    -- (2)
    set W : Ω → ℝ := fun ω ↦ ∑ j ∈ Finset.univ.filter (fun j : Fin m ↦ ¬ (j : ℕ) < s), Y j ω
      with hW
    have hGW : ∀ ω, S m ω - S s ω = W ω := by
      intro ω
      rw [← sum_highPart]
      simp only [hW, highPart]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    have h2 : 1 ≤ ∫ ω, G ω ∂P := by
      have hWint : Integrable W P :=
        integrable_finsetSum _ (fun j _ ↦ (hsub j).integrable)
      have hWmean : ∫ ω, W ω ∂P = 0 := by
        rw [hW, integral_finsetSum _ (fun j _ ↦ (hsub j).integrable)]
        exact Finset.sum_eq_zero (fun j _ ↦ hmean j)
      have hGint : Integrable G P := by
        have := (hsubU (Finset.univ.filter (fun j : Fin m ↦ ¬ (j : ℕ) < s))).integrable_exp_mul l
        refine this.congr (Filter.Eventually.of_forall (fun ω ↦ ?_))
        simp only [hG, hGW, hW]
      calc (1 : ℝ) = ∫ ω, (1 + l * W ω) ∂P := by
            rw [integral_add (integrable_const _) (hWint.const_mul l), integral_const,
              integral_const_mul, hWmean]
            simp
        _ ≤ ∫ ω, G ω ∂P := by
            refine integral_mono ((integrable_const _).add (hWint.const_mul l)) hGint
              (fun ω ↦ ?_)
            simp only [hG, hGW]
            linarith [Real.add_one_le_exp (l * W ω)]
    -- (3) independence
    have hind' : IndepFun F G P := by
      set F' : (Fin m → ℝ) → ℝ :=
        {v | a ≤ psum v s ∧ ∀ r ∈ Finset.range s, psum v r < a}.indicator
          (fun v ↦ Real.exp (l * psum v s)) with hF'
      set G' : (Fin m → ℝ) → ℝ := fun v ↦ Real.exp (l * ∑ j, v j) with hG'
      have hF'm : Measurable F' :=
        ((measurable_psum s).const_mul l).exp.indicator
          (measurableSet_firstPassage (fun r ↦ measurable_psum r) a s)
      have hG'm : Measurable G' :=
        ((Finset.measurable_sum _ (fun j _ ↦ measurable_pi_apply j)).const_mul l).exp
      have h3 := (indep_low_high hmeas hind s).comp hF'm hG'm
      convert h3 using 1
      · funext ω
        have hlow : ∀ r ∈ Finset.range s, psum (lowPart s (fun j ↦ Y j ω)) r = S r ω := by
          intro r hr
          rw [Finset.mem_range] at hr
          exact psum_lowPart hr.le _
        have hlows : psum (lowPart s (fun j ↦ Y j ω)) s = S s ω := psum_lowPart le_rfl _
        simp only [Function.comp, hF', hF]
        by_cases hω : ω ∈ E s
        · have hmem : lowPart s (fun j ↦ Y j ω) ∈
              {v : Fin m → ℝ | a ≤ psum v s ∧ ∀ r ∈ Finset.range s, psum v r < a} := by
            rw [Set.mem_setOf_eq, hlows]
            exact ⟨hω.1, fun r hr ↦ by rw [hlow r hr]; exact hω.2 r hr⟩
          rw [Set.indicator_of_mem hω, Set.indicator_of_mem hmem, hlows]
        · have hmem : lowPart s (fun j ↦ Y j ω) ∉
              {v : Fin m → ℝ | a ≤ psum v s ∧ ∀ r ∈ Finset.range s, psum v r < a} := by
            rw [Set.mem_setOf_eq, hlows]
            rintro ⟨h1, h2⟩
            exact hω ⟨h1, fun r hr ↦ by rw [← hlow r hr]; exact h2 r hr⟩
          rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hmem]
      · funext ω
        simp only [Function.comp, hG', hG]
        rw [sum_highPart]
    have hFm : Measurable F := ((hSmeas s).const_mul l).exp.indicator (hEmeas s)
    have hGm : Measurable G := (((hSmeas m).sub (hSmeas s)).const_mul l).exp
    have h4 : ∫ ω, F ω * G ω ∂P = (∫ ω, F ω ∂P) * (∫ ω, G ω ∂P) :=
      hind'.integral_fun_mul_eq_mul_integral hFm.aestronglyMeasurable hGm.aestronglyMeasurable
    have h5 : ∫ ω, F ω * G ω ∂P = ∫ ω in E s, Real.exp (l * S m ω) ∂P := by
      rw [← integral_indicator (hEmeas s)]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω ↦ ?_))
      by_cases hω : ω ∈ E s
      · simp only [hF, hG, Set.indicator_of_mem hω, ← Real.exp_add]
        ring_nf
      · simp only [hF, Set.indicator_of_notMem hω, zero_mul]
    have hFnn : 0 ≤ ∫ ω, F ω ∂P :=
      integral_nonneg (fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) ω)
    calc Real.exp (l * a) * P.real (E s) ≤ ∫ ω, F ω ∂P := h1
      _ ≤ (∫ ω, F ω ∂P) * (∫ ω, G ω ∂P) := le_mul_of_one_le_right hFnn h2
      _ = ∫ ω in E s, Real.exp (l * S m ω) ∂P := by rw [← h4, h5]
  -- summing up
  have hsum : Real.exp (l * a) * P.real (⋃ s ∈ Finset.range (m+1), E s) ≤
      Real.exp (m * l ^ 2 / 2) := by
    rw [measureReal_biUnion_finset hdisj (fun s _ ↦ hEmeas s), Finset.mul_sum]
    calc ∑ s ∈ Finset.range (m+1), Real.exp (l * a) * P.real (E s)
        ≤ ∑ s ∈ Finset.range (m+1), ∫ ω in E s, Real.exp (l * S m ω) ∂P :=
          Finset.sum_le_sum hper
      _ = ∫ ω in ⋃ s ∈ Finset.range (m+1), E s, Real.exp (l * S m ω) ∂P :=
          (integral_biUnion_finset _ (fun s _ ↦ hEmeas s) hdisj
            (fun s _ ↦ (hexpS m).integrableOn)).symm
      _ ≤ ∫ ω, Real.exp (l * S m ω) ∂P :=
          setIntegral_le_integral (hexpS m)
            (Filter.Eventually.of_forall (fun ω ↦ (Real.exp_pos _).le))
      _ ≤ Real.exp (m * l ^ 2 / 2) := by
          have hmgf := (hsubU Finset.univ).mgf_le l
          have e1 : (fun ω ↦ Real.exp (l * S m ω)) =
              fun ω ↦ Real.exp (l * ∑ j ∈ Finset.univ, Y j ω) := by
            funext ω
            simp only [hSdef]
            rw [psum_all]
          rw [e1]
          unfold mgf at hmgf
          refine hmgf.trans (le_of_eq ?_)
          simp
  rw [hunion]
  have hexp_pos := Real.exp_pos (l * a)
  rw [← le_div_iff₀' hexp_pos, ← Real.exp_sub] at hsum
  refine hsum.trans (le_of_eq ?_)
  congr 1
  rw [hl]
  field_simp
  ring

end Maximal

/-! ## M11 peeling: the tail and excess of `Zmax` -/

section Peeling
variable {k n : ℕ}

lemma geom_exp_telescope (y : ℝ) (hy : 0 < y) (J : ℕ) :
    ∑ j ∈ Finset.range J, (2:ℝ) ^ j * y * Real.exp (-((2:ℝ) ^ j * y)) ≤ 2 := by
  set f : ℕ → ℝ := fun j ↦ Real.exp (-((2:ℝ) ^ j * y / 2)) with hf
  have hterm : ∀ j, (2:ℝ) ^ j * y * Real.exp (-((2:ℝ) ^ j * y)) ≤ 2 * (f j - f (j+1)) := by
    intro j
    set w := (2:ℝ) ^ j * y with hw
    have hw0 : 0 ≤ w := by positivity
    have e1 : f (j+1) = Real.exp (-w) := by
      simp only [hf, pow_succ]; congr 1; rw [hw]; ring
    have e2 : f j = Real.exp (w / 2) * Real.exp (-w) := by
      simp only [hf]; rw [← Real.exp_add]; congr 1; rw [hw]; ring
    rw [e1, e2]
    have h1 := Real.add_one_le_exp (w / 2)
    have h2 := Real.exp_pos (-w)
    nlinarith
  calc ∑ j ∈ Finset.range J, (2:ℝ) ^ j * y * Real.exp (-((2:ℝ) ^ j * y))
      ≤ ∑ j ∈ Finset.range J, 2 * (f j - f (j+1)) := Finset.sum_le_sum (fun j _ ↦ hterm j)
    _ = 2 * (f 0 - f J) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ 2 := by
        have h0 : f 0 ≤ Real.exp 0 := by
          simp only [hf]
          exact Real.exp_le_exp.mpr (by simp only [pow_zero, one_mul]; linarith)
        rw [Real.exp_zero] at h0
        have hJ : 0 < f J := Real.exp_pos _
        linarith

lemma measurable_fold_max {X : Type*} [MeasurableSpace X] (t : Finset ℕ) (g : ℕ → X → ℝ)
    (hg : ∀ s, Measurable (g s)) (b : ℝ) :
    Measurable (fun x ↦ t.fold max b (fun s ↦ g s x)) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      simp only [Finset.fold_insert ha]
      exact (hg a).max ih

lemma measurable_Zmax (i₀ : Fin k) (μs : ℝ) : Measurable (fun ω : Stack k n ↦ Zmax ω i₀ μs) :=
  measurable_fold_max _ (fun s ω ↦ μs - U ω i₀ s)
    (fun s ↦ measurable_const.sub (measurable_U i₀ s)) 0

lemma Zmax_le_sum (ω : Stack k n) (i₀ : Fin k) (μs : ℝ) :
    Zmax ω i₀ μs ≤ ∑ s ∈ Finset.Ico 1 n, |μs - U ω i₀ s| := by
  unfold Zmax
  rw [Finset.fold_max_le]
  refine ⟨Finset.sum_nonneg (fun s _ ↦ abs_nonneg _), fun s hs ↦ ?_⟩
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun s ↦ |μs - U ω i₀ s|) (fun s _ ↦ abs_nonneg _) hs)

lemma integrable_coord (ν : StochasticBandit k) (hν : ∀ i, Integrable id (ν.P i))
    (p : Fin k × Fin (n+1)) : Integrable (fun ω : Stack k n ↦ ω p) (stackMeasure ν n) := by
  unfold stackMeasure
  exact integrable_eval (μ := fun q : Fin k × Fin (n+1) ↦ ν.P q.1) (hν p.1)

lemma integral_coord (ν : StochasticBandit k) (p : Fin k × Fin (n+1)) :
    ∫ ω : Stack k n, ω p ∂(stackMeasure ν n) = banditArmMean ν p.1 := by
  unfold stackMeasure banditArmMean
  exact integral_comp_eval (μ := fun q : Fin k × Fin (n+1) ↦ ν.P q.1) (f := fun x ↦ x)
    aestronglyMeasurable_id

lemma integrable_U (ν : StochasticBandit k) (hν : ∀ i, Integrable id (ν.P i)) (i : Fin k)
    (s : ℕ) : Integrable (fun ω : Stack k n ↦ U ω i s) (stackMeasure ν n) := by
  unfold U
  refine Integrable.add (Integrable.div_const ?_ _) (integrable_const _)
  exact integrable_finsetSum _ (fun r _ ↦ integrable_coord ν hν _)

lemma integrable_Zmax (ν : StochasticBandit k) (hν : ∀ i, Integrable id (ν.P i)) (i₀ : Fin k)
    (μs : ℝ) : Integrable (fun ω ↦ Zmax ω i₀ μs) (stackMeasure ν n) := by
  refine Integrable.mono' (g := fun ω ↦ ∑ s ∈ Finset.Ico 1 n, |μs - U ω i₀ s|) ?_
    (measurable_Zmax i₀ μs).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω ↦ ?_))
  · exact integrable_finsetSum _
      (fun s _ ↦ ((integrable_const _).sub (integrable_U ν hν i₀ s)).abs)
  · rw [Real.norm_eq_abs, abs_of_nonneg (Zmax_nonneg ω i₀ μs)]
    exact Zmax_le_sum ω i₀ μs

lemma logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x := Real.log_nonneg (le_max_left _ _)

lemma logPlus_mono {x y : ℝ} (h : x ≤ y) : logPlus x ≤ logPlus y :=
  Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) (max_le_max le_rfl h)

lemma psum_eq_sum_range {m : ℕ} (f : ℕ → ℝ) {s : ℕ} (hs : s ≤ m) :
    psum (fun j : Fin m ↦ f j) s = ∑ r ∈ Finset.range s, f r := by
  unfold psum
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun r ↦ if r < s then f r else 0),
    ← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨by omega, h⟩

lemma stack_maximal (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν) (i₀ : Fin k)
    {M : ℕ} (hM : M ≤ n + 1) {a : ℝ} (ha : 0 < a) :
    (stackMeasure ν n).real {ω | ∃ s ≤ M, a ≤ ∑ r ∈ Finset.range s,
      (banditArmMean ν i₀ - ω (i₀, Fin.ofNat (n+1) r))} ≤ Real.exp (-a ^ 2 / (2 * M)) := by
  set g : Fin M → Fin k × Fin (n+1) := fun r ↦ (i₀, Fin.ofNat (n+1) r.val) with hg
  have hginj : Function.Injective g := by
    intro r₁ r₂ heq
    simp only [hg, Prod.mk.injEq, true_and] at heq
    have := congrArg Fin.val heq
    simp only [Fin.val_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.ext this
  set Y : Fin M → Stack k n → ℝ := fun r ω ↦ banditArmMean ν i₀ - ω (g r) with hY
  have hmeas : ∀ r, Measurable (Y r) := fun r ↦ measurable_const.sub (measurable_pi_apply _)
  have hind : iIndepFun Y (stackMeasure ν n) := by
    have h1 := (stack_iIndep ν (N := n)).precomp hginj
    have h2 := h1.comp (fun _ x ↦ -x) (fun _ ↦ measurable_neg)
    convert h2 using 1
    funext r ω
    simp [hY, hg]
  have hsub : ∀ r, HasSubgaussianMGF (Y r) 1 (stackMeasure ν n) := by
    intro r
    have := (stack_subG ν hν (g r) (N := n)).neg
    convert this using 1
    funext ω
    simp [hY, hg]
  have hmean : ∀ r, ∫ ω, Y r ω ∂(stackMeasure ν n) = 0 := by
    intro r
    simp only [hY]
    rw [integral_sub (integrable_const _) (integrable_coord ν hν.1 _), integral_const,
      integral_coord]
    simp [hg]
  have h := maximal_hoeffding hmeas hind hsub hmean ha
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    have e := psum_eq_sum_range (fun r ↦ banditArmMean ν i₀ - ω (i₀, Fin.ofNat (n+1) r)) hs
    simp only at e
    simp only [hY, hg]
    rw [e]; exact h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    have e := psum_eq_sum_range (fun r ↦ banditArmMean ν i₀ - ω (i₀, Fin.ofNat (n+1) r)) hs
    simp only at e
    simp only [hY, hg] at h
    rw [e] at h; exact h

theorem Z_tail (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν) (hk : 0 < k)
    (hkn : k ≤ n) (i₀ : Fin k) (hi₀ : banditArmMean ν i₀ = banditOptimalMean ν) {x : ℝ}
    (hx : 0 < x) :
    (stackMeasure ν n).real {ω | x < Zmax ω i₀ (banditOptimalMean ν)} ≤
      16 * k / (n * x ^ 2) := by
  set μs := banditOptimalMean ν with hμs
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  set y := x ^ 2 / 4 with hy
  have hy0 : 0 < y := by positivity
  set m : ℕ → ℕ := fun j ↦ min (2 ^ (j+1)) n with hm
  set ℓ : ℕ → ℝ := fun j ↦ logPlus ((n:ℝ) / ((k:ℝ) * (2:ℝ) ^ (j+1))) with hℓ
  set a : ℕ → ℝ := fun j ↦ (2:ℝ) ^ j * x + Real.sqrt (4 * (2:ℝ) ^ j * ℓ j) with ha
  set B : ℕ → Set (Stack k n) := fun j ↦ {ω | ∃ s ≤ m j, a j ≤ ∑ r ∈ Finset.range s,
      (banditArmMean ν i₀ - ω (i₀, Fin.ofNat (n+1) r))} with hB
  -- Step 1: containment in the union of blocks
  have hsub : {ω | x < Zmax ω i₀ μs} ⊆ ⋃ j ∈ Finset.range n, B j := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    unfold Zmax at hω
    rw [Finset.lt_fold_max] at hω
    rcases hω with h0 | ⟨s, hs, hlt⟩
    · exact absurd h0 (not_lt.mpr hx.le)
    rw [Finset.mem_Ico] at hs
    set j := Nat.log 2 s with hj
    have hj1 : 2 ^ j ≤ s := Nat.pow_log_le_self 2 (by omega)
    have hj2 : s < 2 ^ (j+1) := Nat.lt_pow_succ_log_self (by norm_num) s
    have hjn : j < n := lt_of_lt_of_le Nat.lt_two_pow_self (hj1.trans hs.2.le)
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
    refine ⟨j, hjn, s, ?_, ?_⟩
    · simp only [hm]; omega
    · have hsR : (1:ℝ) ≤ s := by exact_mod_cast hs.1
      have hs0 : (0:ℝ) < s := by linarith
      have hj1R : (2:ℝ) ^ j ≤ s := by exact_mod_cast hj1
      have hj2R : (s:ℝ) ≤ (2:ℝ) ^ (j+1) := by exact_mod_cast hj2.le
      unfold U at hlt
      set S := ∑ r ∈ Finset.range s, ω (i₀, Fin.ofNat (n+1) r) with hS
      set L := logPlus ((n:ℝ) / ((k:ℝ) * (s:ℝ))) with hL
      set b := Real.sqrt ((4 / (s:ℝ)) * L) with hb
      have hL0 : 0 ≤ L := logPlus_nonneg _
      have hℓL : ℓ j ≤ L := by
        simp only [hℓ, hL]
        refine logPlus_mono (div_le_div_of_nonneg_left hnR.le (by positivity) ?_)
        exact mul_le_mul_of_nonneg_left hj2R hkR.le
      have hℓ0 : 0 ≤ ℓ j := logPlus_nonneg _
      -- s * b ≥ sqrt (4 * 2^j * ℓ j)
      have hsb : Real.sqrt (4 * (2:ℝ) ^ j * ℓ j) ≤ s * b := by
        have hb0 : 0 ≤ b := Real.sqrt_nonneg _
        have hsq : (s * b) ^ 2 = 4 * s * L := by
          rw [mul_pow, hb, Real.sq_sqrt (by positivity)]
          field_simp
        calc Real.sqrt (4 * (2:ℝ) ^ j * ℓ j) ≤ Real.sqrt ((s * b) ^ 2) := by
              refine Real.sqrt_le_sqrt ?_
              rw [hsq]
              have := mul_le_mul hj1R hℓL hℓ0 hs0.le
              nlinarith
          _ = s * b := Real.sqrt_sq (by positivity)
      have hsum : ∑ r ∈ Finset.range s, (banditArmMean ν i₀ - ω (i₀, Fin.ofNat (n+1) r)) =
          s * μs - S := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hi₀]
      rw [hsum]
      simp only [ha]
      have h1 : S / s + b < μs - x := by linarith
      rw [div_add' _ _ _ hs0.ne', div_lt_iff₀ hs0] at h1
      have h2 : (2:ℝ) ^ j * x ≤ s * x := mul_le_mul_of_nonneg_right hj1R hx.le
      nlinarith
  -- Step 2 and 3: each block
  have hBj : ∀ j ∈ Finset.range n, (stackMeasure ν n).real (B j) ≤
      2 * k / (n * y) * ((2:ℝ) ^ j * y * Real.exp (-((2:ℝ) ^ j * y))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hP2 : (0:ℝ) < (2:ℝ) ^ j := by positivity
    have hmj : m j ≤ n + 1 := by simp only [hm]; omega
    have hmj1 : 1 ≤ m j := by
      simp only [hm]
      have : 1 ≤ 2 ^ (j+1) := Nat.one_le_two_pow
      omega
    have hmjR : (1:ℝ) ≤ (m j : ℝ) := by exact_mod_cast hmj1
    have hmj2 : (m j : ℝ) ≤ 2 * (2:ℝ) ^ j := by
      have : m j ≤ 2 ^ (j+1) := by simp only [hm]; omega
      have h' : ((m j : ℕ) : ℝ) ≤ ((2 ^ (j+1) : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ] at h'
      linarith
    have hℓ0 : 0 ≤ ℓ j := logPlus_nonneg _
    have ha0 : 0 < a j := by
      simp only [ha]
      have := Real.sqrt_nonneg (4 * (2:ℝ) ^ j * ℓ j)
      have : 0 < (2:ℝ) ^ j * x := by positivity
      linarith
    have hmax := stack_maximal ν hν i₀ hmj ha0
    refine hmax.trans ?_
    -- exponent comparison
    set v := Real.sqrt (4 * (2:ℝ) ^ j * ℓ j) with hv
    have hv2 : v ^ 2 = 4 * (2:ℝ) ^ j * ℓ j := Real.sq_sqrt (by positivity)
    have hv0 : 0 ≤ v := Real.sqrt_nonneg _
    have hexp1 : -(a j) ^ 2 / (2 * (m j : ℝ)) ≤ -((2:ℝ) ^ j * y + ℓ j) := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      have hA : (2:ℝ) ^ j * y + ℓ j ≤ (a j) ^ 2 / (4 * (2:ℝ) ^ j) := by
        rw [le_div_iff₀ (by positivity)]
        simp only [ha, hy]
        rw [← hv]
        have : 0 ≤ (2:ℝ) ^ j * x * v := by positivity
        nlinarith
      have hA0 : 0 ≤ (2:ℝ) ^ j * y + ℓ j := by positivity
      calc ((2:ℝ) ^ j * y + ℓ j) * (2 * (m j : ℝ)) ≤ ((2:ℝ) ^ j * y + ℓ j) * (4 * (2:ℝ) ^ j) :=
            mul_le_mul_of_nonneg_left (by linarith) hA0
        _ ≤ (a j) ^ 2 := by rwa [le_div_iff₀ (by positivity)] at hA
    have hℓexp : Real.exp (-ℓ j) ≤ (k:ℝ) * (2:ℝ) ^ (j+1) / n := by
      simp only [hℓ, logPlus]
      have hq : 0 < (n:ℝ) / ((k:ℝ) * (2:ℝ) ^ (j+1)) := by positivity
      have hM : 0 < max 1 ((n:ℝ) / ((k:ℝ) * (2:ℝ) ^ (j+1))) := lt_of_lt_of_le one_pos (le_max_left _ _)
      rw [Real.exp_neg, Real.exp_log hM]
      have e : (k:ℝ) * (2:ℝ) ^ (j+1) / n = ((n:ℝ) / ((k:ℝ) * (2:ℝ) ^ (j+1)))⁻¹ := by
        rw [inv_div]
      rw [e]
      exact (inv_le_inv₀ hM hq).mpr (le_max_right _ _)
    calc Real.exp (-(a j) ^ 2 / (2 * (m j : ℝ))) ≤ Real.exp (-((2:ℝ) ^ j * y + ℓ j)) :=
          Real.exp_le_exp.mpr hexp1
      _ = Real.exp (-((2:ℝ) ^ j * y)) * Real.exp (-ℓ j) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-((2:ℝ) ^ j * y)) * ((k:ℝ) * (2:ℝ) ^ (j+1) / n) :=
          mul_le_mul_of_nonneg_left hℓexp (Real.exp_pos _).le
      _ = 2 * k / (n * y) * ((2:ℝ) ^ j * y * Real.exp (-((2:ℝ) ^ j * y))) := by
          rw [pow_succ]; field_simp
  -- Step 4: sum
  calc (stackMeasure ν n).real {ω | x < Zmax ω i₀ μs}
      ≤ (stackMeasure ν n).real (⋃ j ∈ Finset.range n, B j) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range n, (stackMeasure ν n).real (B j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range n, 2 * k / (n * y) * ((2:ℝ) ^ j * y * Real.exp (-((2:ℝ) ^ j * y))) :=
        Finset.sum_le_sum hBj
    _ = 2 * k / (n * y) * ∑ j ∈ Finset.range n, (2:ℝ) ^ j * y * Real.exp (-((2:ℝ) ^ j * y)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * k / (n * y) * 2 :=
        mul_le_mul_of_nonneg_left (geom_exp_telescope y hy0 n) (by positivity)
    _ = 16 * k / (n * x ^ 2) := by
        rw [hy]; field_simp; ring


theorem Z_excess (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν) (hk : 0 < k)
    (hkn : k ≤ n) (i₀ : Fin k) (hi₀ : banditArmMean ν i₀ = banditOptimalMean ν) {c : ℝ}
    (hc : 0 < c) :
    ∫ ω, max 0 (Zmax ω i₀ (banditOptimalMean ν) - c) ∂(stackMeasure ν n) ≤ 16 * k / (n * c) := by
  set μs := banditOptimalMean ν with hμs
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hkn)
  set V : Stack k n → ℝ := fun ω ↦ max 0 (Zmax ω i₀ μs - c) with hV
  have hZint := integrable_Zmax ν hν.1 i₀ μs (n := n)
  have hVint : Integrable V (stackMeasure ν n) := by
    refine Integrable.mono' (g := fun ω ↦ |Zmax ω i₀ μs - c|) (hZint.sub (integrable_const c)).abs
      ((measurable_const.max ((measurable_Zmax i₀ μs).sub measurable_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω ↦ ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le (abs_nonneg _) (le_abs_self _)
  have hV0 : 0 ≤ᵐ[stackMeasure ν n] V := Filter.Eventually.of_forall (fun ω ↦ le_max_left _ _)
  rw [hVint.integral_eq_integral_meas_lt hV0]
  set K : ℝ := 16 * k / n with hK
  have hK0 : 0 ≤ K := by positivity
  set g : ℝ → ℝ := fun t ↦ -K / (c + t) with hg
  set g' : ℝ → ℝ := fun t ↦ K / (c + t) ^ 2 with hg'
  have hderiv : ∀ t ∈ Set.Ici (0:ℝ), HasDerivAt g (g' t) t := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have hct : c + t ≠ 0 := by linarith
    have h1 : HasDerivAt (fun t ↦ c + t) 1 t := (hasDerivAt_id t).const_add c
    have h2 := (h1.inv hct).const_mul (-K)
    convert h2 using 1
    simp only [hg']
    field_simp
  have hpos : ∀ t ∈ Set.Ioi (0:ℝ), 0 ≤ g' t := fun t _ ↦ by simp only [hg']; positivity
  have hlim : Filter.Tendsto g Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop (Filter.tendsto_atTop_add_const_left _ c Filter.tendsto_id) (-K)
  have hgint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  calc ∫ t in Set.Ioi 0, (stackMeasure ν n).real {ω | t < V ω}
      ≤ ∫ t in Set.Ioi 0, g' t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t ↦ measureReal_nonneg))
          hgint (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht ↦ ?_))
        have ht0 : (0:ℝ) < t := ht
        have hset : {ω | t < V ω} = {ω | c + t < Zmax ω i₀ μs} := by
          ext ω
          simp only [hV, Set.mem_setOf_eq, lt_max_iff]
          constructor
          · rintro (h | h)
            · exact absurd h (not_lt.mpr ht0.le)
            · linarith
          · intro h; right; linarith
        show (stackMeasure ν n).real {ω | t < V ω} ≤ g' t
        rw [hset]
        refine (Z_tail ν hν hk hkn i₀ hi₀ (by linarith : 0 < c + t)).trans (le_of_eq ?_)
        simp only [hg', hK]
        field_simp
    _ = 16 * k / (n * c) := by
        rw [hval]
        simp only [hg, hK]
        field_simp
        ring

end Peeling

/-! ## M12 assembly of the intermediate bound -/

section Assembly
variable {k n : ℕ}

lemma integrable_kappa (ν : StochasticBandit k) (i : Fin k) (lvl : ℝ) :
    Integrable (fun ω : Stack k n ↦ (kappa ω i lvl : ℝ)) (stackMeasure ν n) := by
  have hm : ∀ s, MeasurableSet {ω : Stack k n | lvl ≤ U ω i s} :=
    fun s ↦ measurableSet_le measurable_const (measurable_U i s)
  have e : (fun ω : Stack k n ↦ (kappa ω i lvl : ℝ)) = fun ω ↦
      ∑ s ∈ Finset.Ico 1 n, {ω : Stack k n | lvl ≤ U ω i s}.indicator (fun _ ↦ (1:ℝ)) ω := by
    funext ω; exact kappa_eq_sum ω i lvl
  rw [e]
  exact integrable_finsetSum _ (fun s _ ↦ (integrable_const _).indicator (hm s))

lemma sqrt_div_mul_self {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.sqrt (x / y) * y = Real.sqrt (x * y) := by
  calc Real.sqrt (x / y) * y = Real.sqrt (x / y) * Real.sqrt (y ^ 2) := by
        rw [Real.sqrt_sq hy.le]
    _ = Real.sqrt (x / y * y ^ 2) := (Real.sqrt_mul (div_nonneg hx hy.le) _).symm
    _ = Real.sqrt (x * y) := by congr 1; field_simp

theorem moss_intermediate (hk : 0 < k) {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsMOSSPolicy n π) (hkn : k ≤ n) :
    banditRegret ν π n ≤
      24 * Real.sqrt ((k : ℝ) * n) +
        Finset.sum (Finset.univ.filter (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i))
          (fun i ↦ banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
  obtain ⟨i₀, hi₀⟩ := exists_optimal_arm hk ν
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hkn)
  set μs := banditOptimalMean ν with hμs
  set D := 8 * Real.sqrt ((k : ℝ) / n) with hD
  have hD0 : 0 ≤ D := by positivity
  set L := Finset.univ.filter (fun i ↦ D < banditGap ν i) with hL
  set P := stackMeasure ν n with hP
  set V : Stack k n → ℝ := fun ω ↦ max 0 (Zmax ω i₀ μs - D / 2) with hV
  have hZint := integrable_Zmax ν hν.1 i₀ μs (n := n)
  have hVint : Integrable V P := by
    refine Integrable.mono' (g := fun ω ↦ |Zmax ω i₀ μs - D / 2|)
      (hZint.sub (integrable_const _)).abs
      ((measurable_const.max ((measurable_Zmax i₀ μs).sub measurable_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω ↦ ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le (abs_nonneg _) (le_abs_self _)
  set R : Stack k n → ℝ := fun ω ↦ n * (D + 2 * V ω) +
      ∑ i ∈ L, banditGap ν i * (1 + (kappa ω i (μs - banditGap ν i / 2) : ℝ)) with hR
  have hRint : Integrable R P := by
    refine Integrable.add (((integrable_const D).add (hVint.const_mul 2)).const_mul _) ?_
    exact integrable_finsetSum _ (fun i _ ↦
      ((integrable_const 1).add (integrable_kappa ν i _)).const_mul _)
  rw [regret_eq_stack (mossArm hπ) ν hν.1 (mossArm_select hπ)]
  have hmono : ∫ ω, ∑ i, banditGap ν i * (armPullCount i (run (mossArm hπ) n n ω) : ℝ) ∂P ≤
      ∫ ω, R ω ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω ↦ ?_)) hRint
      (Filter.Eventually.of_forall (fun ω ↦ ?_))
    · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (banditGap_nonneg ν i) (Nat.cast_nonneg _))
    · exact pathwise hπ ν i₀ D hD0 ω
  refine hmono.trans ?_
  have hA : Integrable (fun ω ↦ (n:ℝ) * (D + 2 * V ω)) P :=
    ((integrable_const D).add (hVint.const_mul 2)).const_mul _
  have hA' : Integrable (fun ω ↦ 2 * V ω) P := hVint.const_mul 2
  have hB : ∀ i, Integrable
      (fun ω ↦ banditGap ν i * (1 + (kappa ω i (μs - banditGap ν i / 2) : ℝ))) P :=
    fun i ↦ ((integrable_const 1).add (integrable_kappa ν i _)).const_mul _
  have hB' : ∀ i, Integrable (fun ω ↦ (kappa ω i (μs - banditGap ν i / 2) : ℝ)) P :=
    fun i ↦ integrable_kappa ν i _
  have hBsum : Integrable
      (fun ω ↦ ∑ i ∈ L, banditGap ν i * (1 + (kappa ω i (μs - banditGap ν i / 2) : ℝ))) P :=
    integrable_finsetSum _ (fun i _ ↦ hB i)
  have hRval : ∫ ω, R ω ∂P = n * (D + 2 * ∫ ω, V ω ∂P) +
      ∑ i ∈ L, banditGap ν i * (1 + ∫ ω, (kappa ω i (μs - banditGap ν i / 2) : ℝ) ∂P) := by
    have e1 : ∫ ω, R ω ∂P = ∫ ω, (n:ℝ) * (D + 2 * V ω) ∂P +
        ∫ ω, ∑ i ∈ L, banditGap ν i * (1 + (kappa ω i (μs - banditGap ν i / 2) : ℝ)) ∂P :=
      integral_add hA hBsum
    have e2 : ∫ ω, (n:ℝ) * (D + 2 * V ω) ∂P = n * (D + 2 * ∫ ω, V ω ∂P) := by
      rw [integral_const_mul]
      congr 1
      have e3 : ∫ ω, (D + 2 * V ω) ∂P = ∫ ω, D ∂P + ∫ ω, 2 * V ω ∂P :=
        integral_add (integrable_const D) hA'
      rw [e3, integral_const, integral_const_mul]
      simp
    have e4 : ∫ ω, ∑ i ∈ L, banditGap ν i * (1 + (kappa ω i (μs - banditGap ν i / 2) : ℝ)) ∂P =
        ∑ i ∈ L, banditGap ν i * (1 + ∫ ω, (kappa ω i (μs - banditGap ν i / 2) : ℝ) ∂P) := by
      rw [integral_finsetSum _ (fun i _ ↦ hB i)]
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      rw [integral_const_mul]
      congr 1
      have e5 : ∫ ω, (1 + (kappa ω i (μs - banditGap ν i / 2) : ℝ)) ∂P =
          ∫ ω, (1:ℝ) ∂P + ∫ ω, (kappa ω i (μs - banditGap ν i / 2) : ℝ) ∂P :=
        integral_add (integrable_const 1) (hB' i)
      rw [e5, integral_const]
      simp
    rw [e1, e2, e4]
  rw [hRval]
  -- bounds
  have hc : 0 < D / 2 := by
    have : 0 < Real.sqrt ((k:ℝ) / n) := Real.sqrt_pos.mpr (div_pos hkR hnR)
    rw [hD]; positivity
  have hVb : ∫ ω, V ω ∂P ≤ 16 * k / (n * (D / 2)) := Z_excess ν hν hk hkn i₀ hi₀ hc (n := n)
  have hκ : ∀ i ∈ L, banditGap ν i * ∫ ω, (kappa ω i (μs - banditGap ν i / 2) : ℝ) ∂P ≤
      12 * Real.sqrt ((n : ℝ) / k) := by
    intro i hi
    rw [hL, Finset.mem_filter] at hi
    exact kappa_integral_le ν hν hk hkn i hi.2
  have hsq1 : Real.sqrt ((k:ℝ) / n) * n = Real.sqrt ((k:ℝ) * n) := sqrt_div_mul_self hkR.le hnR
  have hsq2 : (n:ℝ) * (16 * k / (n * (D / 2))) = 4 * Real.sqrt ((k:ℝ) * n) := by
    have hs : 0 < Real.sqrt ((k:ℝ) / n) := Real.sqrt_pos.mpr (div_pos hkR hnR)
    have hs2 : Real.sqrt ((k:ℝ) / n) ^ 2 * n = k := by
      rw [Real.sq_sqrt (div_pos hkR hnR).le]; field_simp
    rw [← hsq1, hD]
    calc (n:ℝ) * (16 * k / (n * (8 * Real.sqrt ((k:ℝ) / n) / 2)))
        = 4 * k / Real.sqrt ((k:ℝ) / n) := by field_simp; ring
      _ = 4 * (Real.sqrt ((k:ℝ) / n) * n) := by
        rw [div_eq_iff hs.ne']
        linear_combination (-4) * hs2
  have hnD : (n:ℝ) * D = 8 * Real.sqrt ((k:ℝ) * n) := by
    rw [hD, ← hsq1]; ring
  have hsumL : ∑ i ∈ L, banditGap ν i * (1 + ∫ ω, (kappa ω i (μs - banditGap ν i / 2) : ℝ) ∂P) ≤
      ∑ i ∈ L, (banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
    refine Finset.sum_le_sum (fun i hi ↦ ?_)
    have := hκ i hi
    have h0 : 0 ≤ Real.sqrt ((n : ℝ) / k) := Real.sqrt_nonneg _
    rw [mul_add, mul_one]
    linarith
  have hVn : (n:ℝ) * (2 * ∫ ω, V ω ∂P) ≤ 8 * Real.sqrt ((k:ℝ) * n) := by
    have := mul_le_mul_of_nonneg_left hVb hnR.le
    rw [hsq2] at this
    linarith
  have hs0 : 0 ≤ Real.sqrt ((k:ℝ) * n) := Real.sqrt_nonneg _
  calc (n:ℝ) * (D + 2 * ∫ ω, V ω ∂P) +
        ∑ i ∈ L, banditGap ν i * (1 + ∫ ω, (kappa ω i (μs - banditGap ν i / 2) : ℝ) ∂P)
      ≤ 8 * Real.sqrt ((k:ℝ) * n) + 8 * Real.sqrt ((k:ℝ) * n) +
          ∑ i ∈ L, (banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
        rw [mul_add, hnD]; linarith
    _ ≤ 24 * Real.sqrt ((k : ℝ) * n) +
          ∑ i ∈ L, (banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by linarith

/-! ## M13 the minimax corollary -/

theorem moss_minimax {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsMOSSPolicy n π) (hkn : k ≤ n) :
    banditRegret ν π n ≤ 39 * Real.sqrt ((k : ℝ) * n) + ∑ i, banditGap ν i := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact (banditPolicy_zero_false π).elim
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hkn)
  refine (moss_intermediate hk hν hπ hkn).trans ?_
  set L := Finset.univ.filter (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h1 : ∑ i ∈ L, banditGap ν i ≤ ∑ i, banditGap ν i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ ↦ banditGap_nonneg ν i)
  have h2 : (L.card : ℝ) ≤ k := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin k))
      (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < banditGap ν i)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h3 : (k:ℝ) * Real.sqrt ((n:ℝ) / k) = Real.sqrt ((k:ℝ) * n) := by
    rw [mul_comm, sqrt_div_mul_self hnR.le hkR, mul_comm]
  have h0 : 0 ≤ Real.sqrt ((n:ℝ) / k) := Real.sqrt_nonneg _
  have h4 : (L.card : ℝ) * (15 * Real.sqrt ((n:ℝ) / k)) ≤ 15 * Real.sqrt ((k:ℝ) * n) := by
    rw [← h3]
    nlinarith
  linarith

end Assembly

end BanditAlgorithm.MossBuild

set_option maxHeartbeats 4000000 in
open MeasureTheory ProbabilityTheory in
theorem solution {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsMOSSPolicy n π) (hkn : k ≤ n) :
    BanditAlgorithm.banditRegret ν π n ≤
      24 * Real.sqrt ((k : ℝ) * n) +
        Finset.sum
          (Finset.univ.filter
            (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < BanditAlgorithm.banditGap ν i))
          (fun i ↦ BanditAlgorithm.banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
  exact BanditAlgorithm.MossBuild.moss_intermediate hk hν hπ hkn
