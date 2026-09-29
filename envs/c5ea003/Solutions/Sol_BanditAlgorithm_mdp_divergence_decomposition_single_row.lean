-- Prove2me | solution 1 for BanditAlgorithm.mdp_divergence_decomposition_single_row
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-04T04:16:28.755792+00:00
-- url     : https://prove2.me/submissions/7f21eefa-b644-4d8e-a32f-3910ab9134ad

import Definitions.Def_UCRL2ConfidenceSets
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The divergence decomposition for MDPs (L&S eq. (38.22))

Two MDPs that differ in a **single transition row** `(s✱, a✱)` are hard to tell
apart: the only rounds that carry any information about which of the two is
being played are the rounds at which `(s✱, a✱)` is actually chosen.  Every other
round has exactly the same conditional law under both, so it cancels out of the
likelihood ratio, and so does the policy — the learner's own randomisation is
the same in both worlds.

Quantitatively, for every history-dependent policy `π` and horizon `n`

`D(P₀, P_j) = E₀[N_{n-1}(s✱, a✱)] · D(P₀(·|s✱,a✱), P_j(·|s✱,a✱))`,

the count running over the rounds whose successor state is still recorded (the
final round's transition is never observed, so it costs nothing).  This is the
MDP analogue of `bandit_divergence_decomposition` (L&S Lemma 15.1) and is the
content of L&S Exercise 38.30, which the book defers and the solutions manual
does not cover; the argument here is the one of Jaksch–Ortner–Auer, JMLR 11
(2010), Appendix E.

The proof is a chain rule over the `n` rounds.  Mathlib's
`klDiv_compProd_eq_add` peels one round off the trajectory measure, the
push-forward along `Fin.snoc` is a measurable embedding so it is divergence
preserving, and the conditional term collapses twice: first the policy factor
drops out (`klDiv_compProd_left`), then the state kernel is the transition row
of the last pair, which is the same row in both MDPs unless that pair is
`(s✱, a✱)`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal

namespace BanditAlgorithm

variable {S A : ℕ}

/-! ## Appending a round is a measurable embedding -/

/-- Appending one round to a trajectory, as a measurable equivalence. -/
noncomputable def mdpSnocEquiv (S A n : ℕ) :
    (MDPTrajectory S A n × (Fin S × Fin A)) ≃ᵐ MDPTrajectory S A (n + 1) :=
  (MeasurableEquiv.prodComm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin S × Fin A)
      (Fin.last n)).symm

lemma mdpSnocEquiv_apply {S A n : ℕ} (p : MDPTrajectory S A n × (Fin S × Fin A)) :
    mdpSnocEquiv S A n p = Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2 := by
  funext t
  simp [mdpSnocEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last]
  rfl

lemma measurableEmbedding_mdpSnoc (S A n : ℕ) :
    MeasurableEmbedding (fun p : MDPTrajectory S A n × (Fin S × Fin A) ↦
      Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2) := by
  have h : (fun p : MDPTrajectory S A n × (Fin S × Fin A) ↦
      Fin.snoc (α := fun _ ↦ Fin S × Fin A) p.1 p.2) = mdpSnocEquiv S A n := by
    funext p; exact (mdpSnocEquiv_apply p).symm
  rw [h]
  exact (mdpSnocEquiv S A n).measurableEmbedding

/-! ## Counting the informative rounds -/

lemma mdpVisitCount_eq_sum {n : ℕ} (h : MDPTrajectory S A n) (k : ℕ)
    (s : Fin S) (a : Fin A) :
    mdpVisitCount h k s a
      = ∑ i : Fin n, if i.val < k ∧ h i = (s, a) then 1 else 0 := by
  classical
  rw [mdpVisitCount, Finset.card_filter]

/-- Appending a round leaves the count of *informative* rounds — those whose
successor state is still recorded — equal to the full count of the shorter
trajectory. -/
lemma mdpVisitCount_snoc {n : ℕ} (h : MDPTrajectory S A n) (x : Fin S × Fin A)
    (s : Fin S) (a : Fin A) :
    mdpVisitCount (Fin.snoc (α := fun _ ↦ Fin S × Fin A) h x) n s a
      = mdpVisitCount h n s a := by
  classical
  rw [mdpVisitCount_eq_sum, mdpVisitCount_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.is_lt]

/-- The full count is the informative count plus the last round. -/
lemma mdpVisitCount_succ_split {m : ℕ} (h : MDPTrajectory S A (m + 1))
    (s : Fin S) (a : Fin A) :
    mdpVisitCount h (m + 1) s a
      = mdpVisitCount h m s a + (if h (Fin.last m) = (s, a) then 1 else 0) := by
  classical
  rw [mdpVisitCount_eq_sum, mdpVisitCount_eq_sum, Fin.sum_univ_castSucc,
    Fin.sum_univ_castSucc]
  simp [Fin.is_lt, Nat.lt_succ_iff, Fin.le_last]

/-! ## The one-round conditional divergence -/

variable (M₀ M₁ : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A)

/-- The policy factor cancels: the two step kernels differ only through the
state kernel, and the action kernel is shared. -/
lemma klDiv_mdpStepKernel_eq (n : ℕ) (h : MDPTrajectory S A n) :
    klDiv (mdpStepKernel M₀ μ0 π n h) (mdpStepKernel M₁ μ0 π n h)
      = klDiv (mdpStateKernel M₀ μ0 n h) (mdpStateKernel M₁ μ0 n h) := by
  rw [mdpStepKernel, mdpStepKernel,
    Kernel.compProd_apply_eq_compProd_sectR, Kernel.compProd_apply_eq_compProd_sectR]
  exact klDiv_compProd_left _ _ _

/-- The state kernel of round `n + 1` is the transition row of the last
recorded pair. -/
lemma mdpStateKernel_succ_apply (m : ℕ) (h : MDPTrajectory S A (m + 1)) :
    mdpStateKernel M₀ μ0 (m + 1) h
      = (M₀.transitionDist (h (Fin.last m)).1 (h (Fin.last m)).2).toMeasure := by
  rw [mdpStateKernel]
  rfl

variable {M₀ M₁ μ0 π}

section SingleRow

variable {sStar : Fin S} {aStar : Fin A}
  (hrow : ∀ s a, (s, a) ≠ (sStar, aStar) → M₀.P s a = M₁.P s a)

include hrow

/-- Off the distinguished pair the two transition rows agree. -/
lemma transitionDist_eq_of_ne {s : Fin S} {a : Fin A} (hne : (s, a) ≠ (sStar, aStar)) :
    (M₀.transitionDist s a).toMeasure = (M₁.transitionDist s a).toMeasure := by
  have h : M₀.transitionDist s a = M₁.transitionDist s a := by
    have hP := hrow s a hne
    unfold FiniteMDP.transitionDist
    simp only [hP]
  rw [h]

/-- **The stage divergence, in the form the induction needs.**  Only the rounds
at which `(sStar, aStar)` was just played contribute; every other round has the
same conditional law in both MDPs, and the policy contributes nothing in either
case.  So passing from the informative count to the full count costs exactly the
divergence of one more round. -/
lemma count_mul_klDiv_eq {n : ℕ} (h : MDPTrajectory S A n) :
    (mdpVisitCount h n sStar aStar : ℝ≥0∞)
        * klDiv (M₀.transitionDist sStar aStar).toMeasure
            (M₁.transitionDist sStar aStar).toMeasure
      = (mdpVisitCount h (n - 1) sStar aStar : ℝ≥0∞)
          * klDiv (M₀.transitionDist sStar aStar).toMeasure
              (M₁.transitionDist sStar aStar).toMeasure
        + klDiv (mdpStateKernel M₀ μ0 n h) (mdpStateKernel M₁ μ0 n h) := by
  cases n with
  | zero => simp [mdpStateKernel, mdpVisitCount]
  | succ m =>
      rw [mdpStateKernel_succ_apply, mdpStateKernel_succ_apply,
        mdpVisitCount_succ_split]
      simp only [Nat.add_sub_cancel, Nat.cast_add, add_mul]
      congr 1
      by_cases hp : h (Fin.last m) = (sStar, aStar)
      · have h1 : (h (Fin.last m)).1 = sStar := by rw [hp]
        have h2 : (h (Fin.last m)).2 = aStar := by rw [hp]
        rw [h1, h2, if_pos hp]
        simp
      · have hEq := transitionDist_eq_of_ne (s := (h (Fin.last m)).1)
          (a := (h (Fin.last m)).2) hrow (by rw [Prod.mk.eta]; exact hp)
        rw [if_neg hp, hEq]
        simp

/-- The state kernels are absolutely continuous provided the distinguished rows
are. -/
lemma mdpStateKernel_ac
    (hac : (M₀.transitionDist sStar aStar).toMeasure
      ≪ (M₁.transitionDist sStar aStar).toMeasure)
    {n : ℕ} (h : MDPTrajectory S A n) :
    mdpStateKernel M₀ μ0 n h ≪ mdpStateKernel M₁ μ0 n h := by
  cases n with
  | zero => rw [mdpStateKernel]; exact Measure.AbsolutelyContinuous.rfl
  | succ m =>
      rw [mdpStateKernel_succ_apply, mdpStateKernel_succ_apply]
      by_cases hp : h (Fin.last m) = (sStar, aStar)
      · have h1 : (h (Fin.last m)).1 = sStar := by rw [hp]
        have h2 : (h (Fin.last m)).2 = aStar := by rw [hp]
        rw [h1, h2]; exact hac
      · have hEq := transitionDist_eq_of_ne (s := (h (Fin.last m)).1)
          (a := (h (Fin.last m)).2) hrow (by rw [Prod.mk.eta]; exact hp)
        rw [hEq]

lemma mdpStepKernel_ac
    (hac : (M₀.transitionDist sStar aStar).toMeasure
      ≪ (M₁.transitionDist sStar aStar).toMeasure)
    {n : ℕ} (h : MDPTrajectory S A n) :
    mdpStepKernel M₀ μ0 π n h ≪ mdpStepKernel M₁ μ0 π n h := by
  rw [mdpStepKernel, mdpStepKernel,
    Kernel.compProd_apply_eq_compProd_sectR, Kernel.compProd_apply_eq_compProd_sectR]
  exact (mdpStateKernel_ac hrow hac h).compProd_left _

omit hrow in
/-- The informative count does not see the extra round: its integral against the
trajectory measure of `n + 1` rounds is its integral against that of `n`. -/
lemma lintegral_mdpVisitCount_succ (n : ℕ) (s : Fin S) (a : Fin A) :
    ∫⁻ h, (mdpVisitCount h n s a : ℝ≥0∞) ∂(mdpMeasure M₀ μ0 π (n + 1))
      = ∫⁻ h, (mdpVisitCount h n s a : ℝ≥0∞) ∂(mdpMeasure M₀ μ0 π n) := by
  rw [mdpMeasure, lintegral_map Measurable.of_discrete measurable_mdpTrajectorySnoc,
    Measure.lintegral_compProd Measurable.of_discrete]
  refine lintegral_congr fun h ↦ ?_
  simp [mdpVisitCount_snoc]

/-- **The divergence decomposition (L&S eq. (38.22); Jaksch et al. App. E).**
Two MDPs differing in the single transition row `(sStar, aStar)` induce
trajectory laws whose relative entropy is exactly the expected number of
*informative* visits to that pair — the rounds whose successor state is still
recorded — times the divergence of the two rows.  The bound holds for every
history-dependent policy: the policy's own randomisation is identical in the two
worlds and cancels out of the likelihood ratio. -/
theorem mdp_divergence_decomposition_single_row
    (hac : (M₀.transitionDist sStar aStar).toMeasure
      ≪ (M₁.transitionDist sStar aStar).toMeasure) (n : ℕ) :
    klDiv (mdpMeasure M₀ μ0 π n) (mdpMeasure M₁ μ0 π n)
      = (∫⁻ h, (mdpVisitCount h (n - 1) sStar aStar : ℝ≥0∞)
            ∂(mdpMeasure M₀ μ0 π n))
        * klDiv (M₀.transitionDist sStar aStar).toMeasure
            (M₁.transitionDist sStar aStar).toMeasure := by
  induction n with
  | zero => simp [mdpMeasure, mdpVisitCount]
  | succ n ih =>
      -- the right-hand side splits off the last round's contribution
      have hR : (∫⁻ h, (mdpVisitCount h (n + 1 - 1) sStar aStar : ℝ≥0∞)
              ∂(mdpMeasure M₀ μ0 π (n + 1)))
            * klDiv (M₀.transitionDist sStar aStar).toMeasure
                (M₁.transitionDist sStar aStar).toMeasure
          = (∫⁻ h, (mdpVisitCount h (n - 1) sStar aStar : ℝ≥0∞)
                ∂(mdpMeasure M₀ μ0 π n))
              * klDiv (M₀.transitionDist sStar aStar).toMeasure
                  (M₁.transitionDist sStar aStar).toMeasure
            + ∫⁻ h, klDiv (mdpStateKernel M₀ μ0 n h) (mdpStateKernel M₁ μ0 n h)
                ∂(mdpMeasure M₀ μ0 π n) := by
        rw [Nat.add_sub_cancel, lintegral_mdpVisitCount_succ,
          ← lintegral_mul_const _ Measurable.of_discrete]
        simp_rw [count_mul_klDiv_eq (μ0 := μ0) hrow]
        rw [lintegral_add_left Measurable.of_discrete,
          lintegral_mul_const _ Measurable.of_discrete]
      rw [hR, mdpMeasure, mdpMeasure,
        InformationTheory.klDiv_map_measurableEmbedding (measurableEmbedding_mdpSnoc S A n),
        klDiv_compProd_eq_add,
        InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae _ _ _
          (Filter.Eventually.of_forall (fun h ↦ mdpStepKernel_ac hrow hac h)),
        ih]
      congr 1
      exact lintegral_congr fun h ↦ klDiv_mdpStepKernel_eq M₀ M₁ μ0 π n h

omit hrow in
/-- The count never exceeds the horizon. -/
lemma mdpVisitCount_le {n : ℕ} (h : MDPTrajectory S A n) (k : ℕ) (s : Fin S)
    (a : Fin A) : mdpVisitCount h k s a ≤ n := by
  classical
  simpa [mdpVisitCount] using
    Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i ↦ i.val < k ∧ h i = (s, a))

omit hrow in
/-- The count is monotone in the cut-off. -/
lemma mdpVisitCount_mono {n : ℕ} (h : MDPTrajectory S A n) {k l : ℕ} (hkl : k ≤ l)
    (s : Fin S) (a : Fin A) :
    mdpVisitCount h k s a ≤ mdpVisitCount h l s a := by
  classical
  refine Finset.card_le_card fun i hi ↦ ?_
  simp only [mdpVisitCount, Finset.mem_filter] at *
  exact ⟨hi.1, lt_of_lt_of_le hi.2.1 hkl, hi.2.2⟩

omit hrow in
/-- The count as a real-valued sum over the rounds, the form in which the arena
supplies it. -/
lemma mdpVisitCount_cast {n : ℕ} (h : MDPTrajectory S A n) (s : Fin S) (a : Fin A) :
    ((mdpVisitCount h n s a : ℕ) : ℝ)
      = ∑ t : Fin n, if h t = (s, a) then (1 : ℝ) else 0 := by
  classical
  rw [mdpVisitCount_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun t _ ↦ by simp [Fin.is_lt]

omit hrow in
/-- The `ℝ≥0∞`-integral of the count is the Bochner integral of its real cast. -/
lemma lintegral_mdpVisitCount_toReal {n : ℕ} (k : ℕ) (s : Fin S) (a : Fin A) :
    (∫⁻ h, (mdpVisitCount h k s a : ℝ≥0∞) ∂(mdpMeasure M₀ μ0 π n)).toReal
      = ∫ h, ((mdpVisitCount h k s a : ℕ) : ℝ) ∂(mdpMeasure M₀ μ0 π n) := by
  have h1 : ENNReal.ofReal (∫ h, ((mdpVisitCount h k s a : ℕ) : ℝ)
        ∂(mdpMeasure M₀ μ0 π n))
      = ∫⁻ h, (mdpVisitCount h k s a : ℝ≥0∞) ∂(mdpMeasure M₀ μ0 π n) := by
    rw [ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (Filter.Eventually.of_forall fun h ↦ by positivity)]
    exact lintegral_congr fun h ↦ by simp
  rw [← h1, ENNReal.toReal_ofReal]
  exact integral_nonneg fun h ↦ by positivity

/-- **The divergence budget of L&S eq. (38.22), in real arithmetic.**  The form
Step 2 consumes: the trajectory divergence is finite and bounded by the expected
number of visits to the distinguished pair times the divergence of the two rows.
The count here is the full one, over all `n` rounds — the last round's
transition is never observed, so this is an overestimate, which is the safe
direction for a lower-bound proof. -/
theorem mdp_klDiv_le_visitCount
    (hac : (M₀.transitionDist sStar aStar).toMeasure
      ≪ (M₁.transitionDist sStar aStar).toMeasure)
    (hfin : klDiv (M₀.transitionDist sStar aStar).toMeasure
      (M₁.transitionDist sStar aStar).toMeasure ≠ ⊤) (n : ℕ) :
    klDiv (mdpMeasure M₀ μ0 π n) (mdpMeasure M₁ μ0 π n) ≠ ⊤
      ∧ (klDiv (mdpMeasure M₀ μ0 π n) (mdpMeasure M₁ μ0 π n)).toReal
        ≤ (∫ h, ((mdpVisitCount h n sStar aStar : ℕ) : ℝ)
              ∂(mdpMeasure M₀ μ0 π n))
          * (klDiv (M₀.transitionDist sStar aStar).toMeasure
              (M₁.transitionDist sStar aStar).toMeasure).toReal := by
  classical
  set C := klDiv (M₀.transitionDist sStar aStar).toMeasure
    (M₁.transitionDist sStar aStar).toMeasure with hC
  set μ := mdpMeasure M₀ μ0 π n with hμ
  have hcount : ∫⁻ h, (mdpVisitCount h (n - 1) sStar aStar : ℝ≥0∞) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := (n : ℝ≥0∞)) (by simp) ?_
    calc ∫⁻ h, (mdpVisitCount h (n - 1) sStar aStar : ℝ≥0∞) ∂μ
        ≤ ∫⁻ _, (n : ℝ≥0∞) ∂μ := by
          refine lintegral_mono fun h ↦ ?_
          exact Nat.cast_le.mpr (mdpVisitCount_le h (n - 1) sStar aStar)
      _ = (n : ℝ≥0∞) := by rw [lintegral_const, measure_univ, mul_one]
  have hdec := mdp_divergence_decomposition_single_row hrow hac (μ0 := μ0) (π := π) n
  refine ⟨by rw [hdec]; exact ENNReal.mul_ne_top hcount hfin, ?_⟩
  rw [hdec, ENNReal.toReal_mul, lintegral_mdpVisitCount_toReal]
  refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
  refine integral_mono Integrable.of_finite Integrable.of_finite fun h ↦ ?_
  exact Nat.cast_le.mpr (mdpVisitCount_mono h (Nat.sub_le n 1) sStar aStar)

end SingleRow

end BanditAlgorithm


theorem solution {S A : ℕ}
    {M₀ M₁ : BanditAlgorithm.FiniteMDP S A}
    {μ0 : BanditAlgorithm.MDPStateDistribution S} {π : BanditAlgorithm.MDPPolicy S A}
    {sStar : Fin S} {aStar : Fin A}
    (hrow : ∀ (s : Fin S) (a : Fin A), (s, a) ≠ (sStar, aStar) → M₀.P s a = M₁.P s a)
    (hac : (M₀.transitionDist sStar aStar).toMeasure
      ≪ (M₁.transitionDist sStar aStar).toMeasure) (n : ℕ) :
    klDiv (BanditAlgorithm.mdpMeasure M₀ μ0 π n) (BanditAlgorithm.mdpMeasure M₁ μ0 π n)
      = (∫⁻ h, (BanditAlgorithm.mdpVisitCount h (n - 1) sStar aStar : ℝ≥0∞)
            ∂(BanditAlgorithm.mdpMeasure M₀ μ0 π n))
        * klDiv (M₀.transitionDist sStar aStar).toMeasure
            (M₁.transitionDist sStar aStar).toMeasure :=
  BanditAlgorithm.mdp_divergence_decomposition_single_row hrow hac n
