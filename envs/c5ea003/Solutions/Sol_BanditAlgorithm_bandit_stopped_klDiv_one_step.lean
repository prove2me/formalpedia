-- Prove2me | solution 1 for BanditAlgorithm.bandit_stopped_klDiv_one_step
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T16:04:23.502213+00:00
-- url     : https://prove2.me/submissions/5aaa0dd5-d517-40f3-bcbe-641a1aa72a3f

import Definitions.Def_BanditTrajectory
import Theorems.Thm_InformationTheory_klDiv_restrict_add_klDiv_restrict_compl
import Theorems.Thm_InformationTheory_klDiv_le_klDiv_trim_of_trace_eq
import Theorems.Thm_InformationTheory_klDiv_trim_le_of_isFiniteMeasure
import Theorems.Thm_BanditAlgorithm_bandit_prefix_klDiv_one_step_on_event

/-!
Reduction of `BanditAlgorithm.bandit_stopped_klDiv_one_step` (L&S Exercise 14.13, printed p. 197,
specialised to the canonical bandit model of Lemma 15.1, Eq. (15.2), printed pp. 198-199).

Write `S = {τ ≤ n}`. The two stopped σ-algebras satisfy
`F_{τ∧m} = F_τ ⊓ F_m` (`IsStoppingTime.measurableSpace_min_const`), so:

* on `S` the learner has already stopped, and `F_{τ∧(n+1)}` and `F_{τ∧n}` have the same trace;
* on `Sᶜ = {τ > n}` the traces are those of the plain filtration `F_{n+1}` and `F_n`, and the
  comparison becomes the one-step chain rule on the `F_n`-event `Sᶜ`.

Splitting the divergence along `S` (additivity over a measurable partition) and treating the two
halves by these two principles gives the result.
-/

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

namespace BanditAlgorithm

/-- Trimming to a smaller σ-algebra commutes with restricting to a set of that σ-algebra. -/
private lemma trim_restrict_trim {α : Type*} {m m' m₀ : MeasurableSpace α}
    (hmm' : m ≤ m') (hm' : m' ≤ m₀) (ρ : @Measure α m₀) {T : Set α}
    (hT : MeasurableSet[m] T) :
    ((ρ.trim hm').restrict T).trim hmm' = (ρ.trim (hmm'.trans hm')).restrict T := by
  refine @Measure.ext _ m _ _ (fun A hA ↦ ?_)
  have hA' : MeasurableSet[m'] A := hmm' _ hA
  have hT' : MeasurableSet[m'] T := hmm' _ hT
  rw [trim_measurableSet_eq hmm' hA, Measure.restrict_apply hA', Measure.restrict_apply hA,
    trim_measurableSet_eq hm' (hA'.inter hT'), trim_measurableSet_eq (hmm'.trans hm') (hA.inter hT)]

theorem _root_.solution
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ) (n : ℕ) :
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const (n + 1)).measurableSpace
        ((banditTrajMeasure ν π).trim
          (hτ.min_const (n + 1)).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim
          (hτ.min_const (n + 1)).measurableSpace_le) ≤
      @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
          ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
          ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) +
        ∑ i, (banditTrajMeasure ν π)
            {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} *
          klDiv (ν.P i) (ν'.P i) := by
  classical
  set P := banditTrajMeasure ν π with hP
  set Q := banditTrajMeasure ν' π with hQ
  set m₁ := (hτ.min_const n).measurableSpace with hm₁
  set m₂ := (hτ.min_const (n + 1)).measurableSpace with hm₂
  have h₁ : m₁ ≤ _ := (hτ.min_const n).measurableSpace_le
  have h₂ : m₂ ≤ _ := (hτ.min_const (n + 1)).measurableSpace_le
  set S : Set (ℕ → Fin k × ℝ) := {ω | τ ω ≤ (n : ℕ∞)} with hS
  -- the two stopped σ-algebras are nested
  have hm₁₂ : m₁ ≤ m₂ :=
    IsStoppingTime.measurableSpace_mono (hτ.min_const n) (hτ.min_const (n + 1)) fun ω ↦
      min_le_min_left (τ ω) (WithTop.coe_le_coe.mpr (Nat.le_succ n))
  -- `S` lies in the smaller one
  have hSm₁ : MeasurableSet[m₁] S :=
    (IsStoppingTime.measurableSet_min_const_iff hτ S).mpr ⟨hτ.measurableSet_le' n, hτ n⟩
  have hSm₂ : MeasurableSet[m₂] S := hm₁₂ _ hSm₁
  -- comparison with the plain filtration
  have hm₂F : m₂ ≤ banditFiltration k (n + 1) := by
    rw [hm₂, IsStoppingTime.measurableSpace_min_const hτ]; exact inf_le_right
  have hm₁F : m₁ ≤ banditFiltration k n := by
    rw [hm₁, IsStoppingTime.measurableSpace_min_const hτ]; exact inf_le_right
  -- trace of `m₂` on `S` is contained in `m₁`
  have htraceS : ∀ A, MeasurableSet[m₂] A → MeasurableSet[m₁] (A ∩ S) := by
    intro A hA
    have hAτ : MeasurableSet[hτ.measurableSpace] A :=
      ((IsStoppingTime.measurableSet_min_const_iff hτ A).mp hA).1
    exact (hτ.measurableSet_inter_le_const_iff A n).mp (hAτ.inter (hτ.measurableSet_le' n))
  -- trace of `F n` on `Sᶜ` is contained in `m₁`
  have hScFn : MeasurableSet[banditFiltration k n] Sᶜ := (hτ n).compl
  have htraceSc : ∀ B, MeasurableSet[banditFiltration k n] B → MeasurableSet[m₁] (B ∩ Sᶜ) := by
    intro B hB
    refine (IsStoppingTime.measurableSet_min_const_iff hτ (B ∩ Sᶜ)).mpr
      ⟨⟨((banditFiltration k).le n _ (hB.inter hScFn)), fun j ↦ ?_⟩, hB.inter hScFn⟩
    by_cases hj : n < j
    · have h1 : MeasurableSet[banditFiltration k j] B :=
        (banditFiltration k).mono hj.le _ hB
      have h2 : MeasurableSet[banditFiltration k j] Sᶜ :=
        (banditFiltration k).mono hj.le _ hScFn
      exact (h1.inter h2).inter (hτ j)
    · have hempty : B ∩ Sᶜ ∩ {ω | τ ω ≤ (j : ℕ∞)} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_compl_iff, hS, mem_setOf_eq, mem_empty_iff_false, iff_false,
          not_and]
        rintro ⟨-, hnS⟩ hle
        exact hnS (hle.trans (by exact_mod_cast Nat.le_of_not_lt hj))
      exact (@MeasurableSet.empty _ (banditFiltration k j)).congr hempty.symm
  -- finiteness instances for the trimmed measures
  haveI : IsFiniteMeasure (P.trim h₂) :=
    ⟨by rw [trim_measurableSet_eq h₂ MeasurableSet.univ]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure (Q.trim h₂) :=
    ⟨by rw [trim_measurableSet_eq h₂ MeasurableSet.univ]; exact measure_lt_top Q univ⟩
  haveI : IsFiniteMeasure (P.trim h₁) :=
    ⟨by rw [trim_measurableSet_eq h₁ MeasurableSet.univ]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure (Q.trim h₁) :=
    ⟨by rw [trim_measurableSet_eq h₁ MeasurableSet.univ]; exact measure_lt_top Q univ⟩
  have hF₂ : banditFiltration k (n + 1) ≤ _ := (banditFiltration k).le (n + 1)
  have hF₁ : banditFiltration k n ≤ _ := (banditFiltration k).le n
  haveI : IsFiniteMeasure (P.trim hF₂) :=
    ⟨by rw [trim_measurableSet_eq hF₂ MeasurableSet.univ]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure (Q.trim hF₂) :=
    ⟨by rw [trim_measurableSet_eq hF₂ MeasurableSet.univ]; exact measure_lt_top Q univ⟩
  haveI : IsFiniteMeasure (P.trim hF₁) :=
    ⟨by rw [trim_measurableSet_eq hF₁ MeasurableSet.univ]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure (Q.trim hF₁) :=
    ⟨by rw [trim_measurableSet_eq hF₁ MeasurableSet.univ]; exact measure_lt_top Q univ⟩
  have hScm₂ : MeasurableSet[m₂] Sᶜ := hSm₂.compl
  have hScm₁ : MeasurableSet[m₁] Sᶜ := hSm₁.compl
  -- the restricted measures live on `S` (resp. `Sᶜ`)
  have hnullS : ∀ {m : MeasurableSpace (ℕ → Fin k × ℝ)} (ρ : @Measure _ m)
      (T : Set (ℕ → Fin k × ℝ)), MeasurableSet[m] Tᶜ → (ρ.restrict T) Tᶜ = 0 := by
    intro m ρ T hT
    rw [Measure.restrict_apply hT, Set.compl_inter_self, measure_empty]
  -- STEP 1 : split along `S`
  have split₂ := @InformationTheory.klDiv_restrict_add_klDiv_restrict_compl _ m₂
    (P.trim h₂) (Q.trim h₂) _ _ S hSm₂
  have split₁ := @InformationTheory.klDiv_restrict_add_klDiv_restrict_compl _ m₁
    (P.trim h₁) (Q.trim h₁) _ _ S hSm₁
  -- STEP 2 : on `S` the finer stopped σ-algebra adds nothing
  have stepS : @klDiv _ m₂ ((P.trim h₂).restrict S) ((Q.trim h₂).restrict S) ≤
      @klDiv _ m₁ ((P.trim h₁).restrict S) ((Q.trim h₁).restrict S) := by
    have := InformationTheory.klDiv_le_klDiv_trim_of_trace_eq hm₁₂
      ((P.trim h₂).restrict S) ((Q.trim h₂).restrict S)
      (hnullS (P.trim h₂) S hScm₂) (hnullS (Q.trim h₂) S hScm₂) htraceS
    rwa [trim_restrict_trim hm₁₂ h₂ P hSm₁, trim_restrict_trim hm₁₂ h₂ Q hSm₁] at this
  -- STEP 3 : on `Sᶜ` we descend to the plain filtration, apply the one-step chain rule, come back
  have stepSc : @klDiv _ m₂ ((P.trim h₂).restrict Sᶜ) ((Q.trim h₂).restrict Sᶜ) ≤
      @klDiv _ m₁ ((P.trim h₁).restrict Sᶜ) ((Q.trim h₁).restrict Sᶜ) +
        ∑ i, P {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} * klDiv (ν.P i) (ν'.P i) := by
    have hScF₂ : MeasurableSet[banditFiltration k (n + 1)] Sᶜ :=
      (banditFiltration k).mono (Nat.le_succ n) _ hScFn
    -- (i) data processing : `m₂ ≤ F (n+1)`
    have hdp : @klDiv _ m₂ ((P.trim h₂).restrict Sᶜ) ((Q.trim h₂).restrict Sᶜ) ≤
        @klDiv _ (banditFiltration k (n + 1))
          ((P.trim hF₂).restrict Sᶜ) ((Q.trim hF₂).restrict Sᶜ) := by
      have := InformationTheory.klDiv_trim_le_of_isFiniteMeasure hm₂F
        ((P.trim hF₂).restrict Sᶜ) ((Q.trim hF₂).restrict Sᶜ)
      rwa [trim_restrict_trim hm₂F hF₂ P hScm₂, trim_restrict_trim hm₂F hF₂ Q hScm₂] at this
    -- (ii) the one-step chain rule on the `F n`-event `Sᶜ`
    have hchain := BanditAlgorithm.bandit_prefix_klDiv_one_step_on_event ν ν' π n Sᶜ hScFn
    -- (iii) climb back to `m₁`
    have hback : @klDiv _ (banditFiltration k n)
        ((P.trim hF₁).restrict Sᶜ) ((Q.trim hF₁).restrict Sᶜ) ≤
        @klDiv _ m₁ ((P.trim h₁).restrict Sᶜ) ((Q.trim h₁).restrict Sᶜ) := by
      have := InformationTheory.klDiv_le_klDiv_trim_of_trace_eq hm₁F
        ((P.trim hF₁).restrict Sᶜ) ((Q.trim hF₁).restrict Sᶜ)
        (hnullS (P.trim hF₁) Sᶜ (by simpa using hScFn))
        (hnullS (Q.trim hF₁) Sᶜ (by simpa using hScFn)) htraceSc
      rwa [trim_restrict_trim hm₁F hF₁ P hScm₁, trim_restrict_trim hm₁F hF₁ Q hScm₁] at this
    -- the increment term is the same set
    have hsets : ∀ i : Fin k, Sᶜ ∩ {ω | (ω n).1 = i} = {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} := by
      intro i
      ext ω
      simp only [hS, mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_le]
    calc @klDiv _ m₂ ((P.trim h₂).restrict Sᶜ) ((Q.trim h₂).restrict Sᶜ)
        ≤ @klDiv _ (banditFiltration k (n + 1))
            ((P.trim hF₂).restrict Sᶜ) ((Q.trim hF₂).restrict Sᶜ) := hdp
      _ ≤ @klDiv _ (banditFiltration k n)
            ((P.trim hF₁).restrict Sᶜ) ((Q.trim hF₁).restrict Sᶜ) +
            ∑ i, P (Sᶜ ∩ {ω | (ω n).1 = i}) * klDiv (ν.P i) (ν'.P i) := hchain
      _ ≤ @klDiv _ m₁ ((P.trim h₁).restrict Sᶜ) ((Q.trim h₁).restrict Sᶜ) +
            ∑ i, P {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} * klDiv (ν.P i) (ν'.P i) := by
            refine add_le_add hback (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
            rw [hsets i]
  -- STEP 4 : reassemble
  rw [split₂, split₁]
  calc @klDiv _ m₂ ((P.trim h₂).restrict S) ((Q.trim h₂).restrict S)
        + @klDiv _ m₂ ((P.trim h₂).restrict Sᶜ) ((Q.trim h₂).restrict Sᶜ)
      ≤ @klDiv _ m₁ ((P.trim h₁).restrict S) ((Q.trim h₁).restrict S)
        + (@klDiv _ m₁ ((P.trim h₁).restrict Sᶜ) ((Q.trim h₁).restrict Sᶜ) +
            ∑ i, P {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} * klDiv (ν.P i) (ν'.P i)) :=
        add_le_add stepS stepSc
    _ = _ := by rw [← add_assoc]

end BanditAlgorithm
