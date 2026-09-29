-- Prove2me | solution 1 for MarkovEntanglement.rmab_entanglement_le_configuration_deviation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-31T00:46:10.034999+00:00
-- url     : https://prove2.me/submissions/620c707f-6606-4086-b349-1206f3df23ce

import Definitions.Def_markov_entanglement_meanfield
import Theorems.Thm_MarkovEntanglement_separable_apply_local_reward

open scoped BigOperators
open MarkovEntanglement


/-! Proposition 1 with nonnegative weights.  The accepted proof of
`weakly_coupled_entanglement_le_policy_mismatch` uses the strict positivity of `μ` only to
derive `0 ≤ μ p`; this is that proof verbatim, with the weakened hypothesis. -/
private theorem prop1_nonneg
    {N : ℕ} {St Act : Fin N → Type*}
    [∀ i, Fintype (St i)] [∀ i, DecidableEq (St i)]
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    (P : JointState St → JointAction Act → JointState St → ℝ)
    (Pl : ∀ i, St i → Act i → St i → ℝ)
    (hPl : IsLocalKernel Pl) (hwc : IsWeaklyCoupled P Pl)
    (π : JointState St → JointAction Act → ℝ) (hπ : IsJointPolicy π)
    (μ : Joint (StateAction St Act) → ℝ) (hμ0 : ∀ p, 0 ≤ μ p)
    (hstat : IsStationary (inducedTransition P π) μ)
    (i : Fin N) (πl : St i → Act i → ℝ) (hπl : IsLocalPolicy πl) :
    entanglementN i μ (inducedTransition P π) ≤ policyMismatch i π μ πl := by
  classical
  set T := inducedTransition P π with hT
  set sp : Joint (StateAction St Act) → JointState St := fun p j => (p j).1 with hsp
  set ap : Joint (StateAction St Act) → JointAction Act := fun p j => (p j).2 with hap
  -- pinning one coordinate of a product kernel leaves that agent's kernel
  have hPabs : ∀ (s : JointState St) (a : JointAction Act) (s' : JointState St),
      0 ≤ P s a s' := by
    intro s a s'
    rw [hwc s a s']
    exact Finset.prod_nonneg (fun j _ => hPl.1 j (s j) (a j) (s' j))
  have hpin : ∀ (s : JointState St) (a : JointAction Act) (t : St i),
      ∑ s' : JointState St, (if s' i = t then P s a s' else 0) = Pl i (s i) (a i) t := by
    intro s a t
    have hA : ∀ j, IsTransitionMatrix (fun x y => Pl j x (a j) y : Matrix (St j) (St j) ℝ) :=
      fun j => ⟨fun x y => hPl.1 j x (a j) y, fun x => hPl.2 j x (a j)⟩
    have h := MarkovEntanglement.separable_apply_local_reward
      (S := St) (K := 1) (fun _ => (1:ℝ))
      (fun _ j => (fun x y => Pl j x (a j) y : Matrix (St j) (St j) ℝ))
      (fun _ j => hA j) (by simp) i (fun y => if y = t then (1:ℝ) else 0) s
    simp only [Fin.sum_univ_one, one_smul, one_mul] at h
    calc ∑ s' : JointState St, (if s' i = t then P s a s' else 0)
        = ∑ s' : JointState St, tensorProdN
            (fun j => (fun x y => Pl j x (a j) y : Matrix (St j) (St j) ℝ)) s s'
              * (if s' i = t then (1:ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [hwc s a s']
          by_cases h1 : s' i = t <;> simp [h1, tensorProdN]
      _ = ∑ y : St i, Pl i (s i) (a i) y * (if y = t then (1:ℝ) else 0) := h
      _ = Pl i (s i) (a i) t := by simp
  -- the marginal of the induced transition onto agent `i`
  have hmarg : ∀ (p : Joint (StateAction St Act)) (y : St i × Act i),
      marginalN i T p y
        = ∑ s' : JointState St,
            (if s' i = y.1 then P (sp p) (ap p) s' * policyMarginal i π s' y.2 else 0) := by
    intro p y
    rw [marginalN]
    rw [← Equiv.sum_comp (splitStateAction (St := St) (Act := Act)).symm]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    by_cases h1 : s' i = y.1
    · rw [if_pos h1, policyMarginal, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      by_cases h2 : a' i = y.2
      · have : ((splitStateAction (St := St) (Act := Act)).symm (s', a')) i = y := by
          simp [splitStateAction, h1, h2, Prod.ext_iff]
        rw [if_pos this, if_pos h2, hT, inducedTransition]
        rfl
      · have : ¬ (((splitStateAction (St := St) (Act := Act)).symm (s', a')) i = y) := by
          simp [splitStateAction, Prod.ext_iff]
          intro _; exact h2
        rw [if_neg this, if_neg h2, mul_zero]
    · rw [if_neg h1]
      refine Finset.sum_eq_zero (fun a' _ => ?_)
      refine if_neg ?_
      simp [splitStateAction, Prod.ext_iff]
      intro hc; exact absurd hc h1
  -- the occupancy state marginal is the pushforward of `μ` through `P`
  have hocc : ∀ s' : JointState St,
      occupancyStateMarginal μ s' = ∑ p, μ p * P (sp p) (ap p) s' := by
    intro s'
    rw [occupancyStateMarginal]
    calc ∑ q : Joint (StateAction St Act), (if (fun j => (q j).1) = s' then μ q else 0)
        = ∑ q : Joint (StateAction St Act),
            (if (fun j => (q j).1) = s' then (∑ p, μ p * T p q) else 0) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          by_cases h1 : (fun j => (q j).1) = s'
          · rw [if_pos h1, if_pos h1, hstat q]
          · rw [if_neg h1, if_neg h1]
      _ = ∑ q : Joint (StateAction St Act), ∑ p,
            (if (fun j => (q j).1) = s' then μ p * T p q else 0) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          by_cases h1 : (fun j => (q j).1) = s' <;> simp [h1]
      _ = ∑ p, ∑ q : Joint (StateAction St Act),
            (if (fun j => (q j).1) = s' then μ p * T p q else 0) := Finset.sum_comm
      _ = ∑ p, μ p * P (sp p) (ap p) s' := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          have hin : ∑ q : Joint (StateAction St Act),
              (if (fun j => (q j).1) = s' then T p q else 0)
                = P (sp p) (ap p) s' := by
            rw [← Equiv.sum_comp (splitStateAction (St := St) (Act := Act)).symm]
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single s']
            · have : ∑ a' : JointAction Act, T p ((splitStateAction).symm (s', a'))
                  = P (sp p) (ap p) s' * ∑ a' : JointAction Act, π s' a' := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun a' _ => ?_)
                rw [hT, inducedTransition]
                rfl
              have hstrip : ∀ a' : JointAction Act,
                  (if (fun j => (((splitStateAction (St := St) (Act := Act)).symm
                        (s', a')) j).1) = s'
                   then T p ((splitStateAction (St := St) (Act := Act)).symm (s', a'))
                   else 0)
                  = T p ((splitStateAction (St := St) (Act := Act)).symm (s', a')) :=
                fun a' => if_pos rfl
              rw [Finset.sum_congr rfl (fun a' _ => hstrip a'), this, hπ.2 s', mul_one]
            · intro b _ hb
              refine Finset.sum_eq_zero (fun a' _ => ?_)
              refine if_neg ?_
              simpa [splitStateAction] using hb
            · intro h; exact absurd (Finset.mem_univ _) h
          calc ∑ q : Joint (StateAction St Act),
                (if (fun j => (q j).1) = s' then μ p * T p q else 0)
              = ∑ q : Joint (StateAction St Act),
                  μ p * (if (fun j => (q j).1) = s' then T p q else 0) := by
                refine Finset.sum_congr rfl (fun q _ => ?_)
                by_cases h1 : (fun j => (q j).1) = s' <;> simp [h1]
            _ = μ p * P (sp p) (ap p) s' := by rw [← Finset.mul_sum, hin]
  -- the candidate local transition: move with agent `i`'s kernel, then act with `πl`
  set Pcand : Matrix (St i × Act i) (St i × Act i) ℝ :=
    fun x y => Pl i x.1 x.2 y.1 * πl y.1 y.2 with hPcand
  have hPcandT : IsTransitionMatrix Pcand := by
    constructor
    · intro x y
      exact mul_nonneg (hPl.1 i x.1 x.2 y.1) (hπl.1 y.1 y.2)
    · intro x
      rw [Fintype.sum_prod_type]
      calc ∑ y1 : St i, ∑ y2 : Act i, Pl i x.1 x.2 y1 * πl y1 y2
          = ∑ y1 : St i, Pl i x.1 x.2 y1 := by
            refine Finset.sum_congr rfl (fun y1 _ => ?_)
            rw [← Finset.mul_sum, hπl.2 y1, mul_one]
        _ = 1 := hPl.2 i x.1 x.2
  have hnn : ∀ Pi : Matrix (St i × Act i) (St i × Act i) ℝ, 0 ≤ muAgentTVDistN i μ T Pi := by
    intro Pi
    refine Finset.sum_nonneg (fun p _ => mul_nonneg (hμ0 p) ?_)
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun t _ => abs_nonneg _))
  have hEle : entanglementN i μ T ≤ muAgentTVDistN i μ T Pcand := by
    refine csInf_le ⟨0, ?_⟩ ⟨Pcand, hPcandT, rfl⟩
    rintro x ⟨Pi, -, rfl⟩
    exact hnn Pi
  refine le_trans hEle ?_
  set D : JointState St → ℝ := fun s' =>
    ∑ a2 : Act i, |policyMarginal i π s' a2 - πl (s' i) a2| with hD
  have hper : ∀ p : Joint (StateAction St Act),
      ∑ y : St i × Act i, |marginalN i T p y - Pcand (p i) y|
        ≤ ∑ s' : JointState St, P (sp p) (ap p) s' * D s' := by
    intro p
    have hdiff : ∀ y : St i × Act i, marginalN i T p y - Pcand (p i) y
        = ∑ s' : JointState St, (if s' i = y.1 then
            P (sp p) (ap p) s' * (policyMarginal i π s' y.2 - πl (s' i) y.2) else 0) := by
      intro y
      rw [hmarg p y, hPcand]
      have h2 : (Pl i (p i).1 (p i).2 y.1) * πl y.1 y.2
          = ∑ s' : JointState St, (if s' i = y.1 then
              P (sp p) (ap p) s' * πl (s' i) y.2 else 0) := by
        rw [← hpin (sp p) (ap p) y.1, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun s' _ => ?_)
        by_cases h1 : s' i = y.1 <;> simp [h1]
      show _ - (Pl i (p i).1 (p i).2 y.1) * πl y.1 y.2 = _
      rw [h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun s' _ => ?_)
      by_cases h1 : s' i = y.1
      · simp only [if_pos h1]; ring
      · simp [h1]
    calc ∑ y : St i × Act i, |marginalN i T p y - Pcand (p i) y|
        ≤ ∑ y : St i × Act i, ∑ s' : JointState St, (if s' i = y.1 then
            P (sp p) (ap p) s' * |policyMarginal i π s' y.2 - πl (s' i) y.2| else 0) := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          rw [hdiff y]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun s' _ => ?_))
          by_cases h1 : s' i = y.1
          · rw [if_pos h1, if_pos h1, abs_mul, abs_of_nonneg (hPabs (sp p) (ap p) s')]
          · simp [h1]
      _ = ∑ s' : JointState St, P (sp p) (ap p) s' * D s' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [hD, Finset.mul_sum, Fintype.sum_prod_type]
          rw [Finset.sum_eq_single (s' i)]
          · refine Finset.sum_congr rfl (fun a2 _ => by simp)
          · intro b _ hb
            exact Finset.sum_eq_zero (fun a2 _ => if_neg (Ne.symm hb))
          · intro h; exact absurd (Finset.mem_univ _) h
  have hfin : ∑ p, μ p * (∑ s' : JointState St, P (sp p) (ap p) s' * D s')
      = ∑ s' : JointState St, occupancyStateMarginal μ s' * D s' := by
    calc ∑ p, μ p * (∑ s' : JointState St, P (sp p) (ap p) s' * D s')
        = ∑ p, ∑ s' : JointState St, μ p * (P (sp p) (ap p) s' * D s') :=
          Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)
      _ = ∑ s' : JointState St, ∑ p, μ p * (P (sp p) (ap p) s' * D s') := Finset.sum_comm
      _ = ∑ s' : JointState St, occupancyStateMarginal μ s' * D s' := by
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [hocc s', Finset.sum_mul]
          exact Finset.sum_congr rfl (fun p _ => by ring)
  calc muAgentTVDistN i μ T Pcand
      = ∑ p, μ p * ((1 / 2) * ∑ y : St i × Act i,
          |marginalN i T p y - Pcand (p i) y|) := rfl
    _ ≤ ∑ p, μ p * ((1 / 2) * ∑ s' : JointState St, P (sp p) (ap p) s' * D s') := by
        refine Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left ?_ (hμ0 p))
        exact mul_le_mul_of_nonneg_left (hper p) (by norm_num)
    _ = (1 / 2) * ∑ p, μ p * (∑ s' : JointState St, P (sp p) (ap p) s' * D s') := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = (1 / 2) * ∑ s' : JointState St, occupancyStateMarginal μ s' * D s' := by rw [hfin]
    _ = policyMismatch i π μ πl := rfl

section Rmab

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! Helper lemmas about configurations and the index policy, re-proved from the layer
(the corresponding lemmas inside other solutions are private there). -/

private lemma cast_nat_sub_eq_max (a b : ℕ) :
    ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - (b : ℝ)) := by
  by_cases h : b ≤ a
  · have h' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub h, max_eq_right (by linarith)]
  · have h' : (a : ℝ) ≤ (b : ℝ) := by
      have : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_le h)
      exact_mod_cast this
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_le h)),
      max_eq_left (by linarith)]
    norm_num

private lemma sum_fiber {N : ℕ} (s : Fin N → S) (F : S → ℝ) :
    (∑ i : Fin N, F (s i)) = ∑ x : S, (stateCount s x : ℝ) * F x := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ s fun i => F (s i)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcst : ∀ i ∈ Finset.univ.filter fun i => s i = x, F (s i) = F x := by
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl hcst, Finset.sum_const, nsmul_eq_mul]
  rfl

private lemma higherPriorityMass_configuration
    {N : ℕ} (ν : S → ℝ) (s : Fin N → S) (x : S) :
    higherPriorityMass ν (configuration s) x
      = (higherPriorityCount ν s x : ℝ) / (N : ℝ) := by
  unfold higherPriorityMass higherPriorityCount configuration
  rw [Nat.cast_sum, Finset.sum_div]

private lemma activateFraction_configuration
    {N : ℕ} (hN : 0 < N) (ν : S → ℝ) (M : ℕ) (s : Fin N → S) (x : S) :
    activateFraction ν ((M : ℝ) / (N : ℝ)) (configuration s) x
      = (activateCount ν M s x : ℝ) / (N : ℝ) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsub : (M : ℝ) / (N : ℝ) - (higherPriorityCount ν s x : ℝ) / (N : ℝ)
      = ((M : ℝ) - (higherPriorityCount ν s x : ℝ)) / (N : ℝ) := by ring
  have hmax : max (0 : ℝ) (((M : ℝ) - (higherPriorityCount ν s x : ℝ)) / (N : ℝ))
      = (max 0 ((M : ℝ) - (higherPriorityCount ν s x : ℝ))) / (N : ℝ) := by
    rw [← max_div_div_right hN'.le, zero_div]
  calc activateFraction ν ((M : ℝ) / (N : ℝ)) (configuration s) x
      = min ((stateCount s x : ℝ) / (N : ℝ))
          (max 0 ((M : ℝ) / (N : ℝ)
            - (higherPriorityCount ν s x : ℝ) / (N : ℝ))) := by
        unfold activateFraction
        rw [higherPriorityMass_configuration]
        unfold configuration
        rfl
    _ = min ((stateCount s x : ℝ) / (N : ℝ))
          ((max 0 ((M : ℝ) - (higherPriorityCount ν s x : ℝ))) / (N : ℝ)) := by
        rw [hsub, hmax]
    _ = (min (stateCount s x : ℝ)
          (max 0 ((M : ℝ) - (higherPriorityCount ν s x : ℝ)))) / (N : ℝ) :=
        min_div_div_right hN'.le _ _
    _ = (activateCount ν M s x : ℝ) / (N : ℝ) := by
        unfold activateCount
        rw [Nat.cast_min, cast_nat_sub_eq_max]

private lemma configuration_mul_indexActivationProb
    {N : ℕ} (hN : 0 < N) (ν : S → ℝ) (M : ℕ) (s : Fin N → S) (x : S) :
    configuration s x * indexActivationProb ν M s x
      = activateFraction ν ((M : ℝ) / (N : ℝ)) (configuration s) x := by
  rw [activateFraction_configuration hN]
  by_cases hc : stateCount s x = 0
  · have hle : activateCount ν M s x ≤ stateCount s x := by
      unfold activateCount; exact min_le_left _ _
    have hz : activateCount ν M s x = 0 := by omega
    unfold configuration indexActivationProb
    simp [hc, hz]
  · unfold configuration indexActivationProb
    rw [if_neg hc]
    have hcR : ((stateCount s x : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hc
    field_simp

/-! Permutation invariance: everything the index policy computes depends on the joint state
only through its configuration, which is invariant under permuting the agents. -/

private lemma stateCount_comp_perm {N : ℕ} (s : Fin N → S) (σ : Equiv.Perm (Fin N)) (x : S) :
    stateCount (s ∘ σ) x = stateCount s x := by
  classical
  unfold stateCount
  refine Finset.card_bij (fun k _ => σ k) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at ha ⊢
    exact ha
  · intro a _ b _ h
    exact σ.injective h
  · intro b hb
    refine ⟨σ.symm b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hb ⊢
    simpa using hb

private lemma indexActivationProb_comp_perm {N : ℕ} (ν : S → ℝ) (M : ℕ)
    (s : Fin N → S) (σ : Equiv.Perm (Fin N)) (x : S) :
    indexActivationProb ν M (s ∘ σ) x = indexActivationProb ν M s x := by
  have hcount : ∀ y, stateCount (s ∘ σ) y = stateCount s y := stateCount_comp_perm s σ
  have hhigher : higherPriorityCount ν (s ∘ σ) x = higherPriorityCount ν s x := by
    unfold higherPriorityCount
    exact Finset.sum_congr rfl fun y _ => hcount y
  unfold indexActivationProb activateCount
  rw [hcount, hhigher]

private lemma occupancyStateMarginal_comp_perm {N : ℕ}
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (hexch : IsExchangeableDist (X := S × Bool) μ)
    (s : Fin N → S) (σ : Equiv.Perm (Fin N)) :
    occupancyStateMarginal μ (s ∘ σ) = occupancyStateMarginal μ s := by
  classical
  unfold occupancyStateMarginal
  rw [← Equiv.sum_comp (Equiv.piCongrLeft' (fun _ : Fin N => S × Bool) σ.symm)
    (fun q => if (fun j => (q j).1) = s ∘ σ then μ q else 0)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have he : (Equiv.piCongrLeft' (fun _ : Fin N => S × Bool) σ.symm) q = q ∘ σ := by
    funext j
    show q (σ.symm.symm j) = q (σ j)
    rw [Equiv.symm_symm]
  rw [he]
  have hcond : ((fun j => ((q ∘ σ) j).1) = s ∘ σ) ↔ ((fun j => (q j).1) = s) := by
    constructor
    · intro h
      funext j
      have := congrFun h (σ.symm j)
      simpa using this
    · intro h
      funext j
      simpa using congrFun h (σ j)
  by_cases h1 : (fun j => (q j).1) = s
  · rw [if_pos (hcond.mpr h1), if_pos h1, hexch σ q]
  · rw [if_neg (fun hc => h1 (hcond.mp hc)), if_neg h1]

/-! The pointwise estimate: the activation probability of the index policy at a joint state,
weighted by the occupancy of the state, deviates from the mean-field limiting policy at
`mstar` by at most `|S| · ‖m − m✦‖_∞`. -/

private lemma abs_le_supNorm (v : S → ℝ) (x : S) : |v x| ≤ supNorm v := by
  unfold supNorm
  exact le_ciSup (f := fun z : S => |v z|)
    (Set.Finite.bddAbove (Set.finite_range fun z : S => |v z|)) x

private lemma min_lipschitz (a b a' b' : ℝ) :
    |min a b - min a' b'| ≤ max |a - a'| |b - b'| := by
  set c := max |a - a'| |b - b'| with hc
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (le_max_left _ _)
  have key : ∀ u v u' v' : ℝ, |u - u'| ≤ c → |v - v'| ≤ c →
      min u v - min u' v' ≤ c := by
    intro u v u' v' hu hv
    have h1 : u ≤ u' + c := by
      have := le_abs_self (u - u'); linarith
    have h2 : v ≤ v' + c := by
      have := le_abs_self (v - v'); linarith
    have h3 : min u v ≤ min (u' + c) (v' + c) := min_le_min h1 h2
    rw [min_add_add_right] at h3
    linarith
  have hA : |a - a'| ≤ c := le_max_left _ _
  have hB : |b - b'| ≤ c := le_max_right _ _
  have hA' : |a' - a| ≤ c := by rwa [abs_sub_comm]
  have hB' : |b' - b| ≤ c := by rwa [abs_sub_comm]
  rw [abs_sub_le_iff]
  exact ⟨key a b a' b' hA hB, key a' b' a b hA' hB'⟩

private lemma max_zero_lipschitz (u v : ℝ) : |max 0 u - max 0 v| ≤ |u - v| := by
  have key : ∀ w z : ℝ, max 0 w - max 0 z ≤ |w - z| := by
    intro w z
    have h1 : w ≤ z + |w - z| := by
      have := le_abs_self (w - z); linarith
    have h2 : max 0 w ≤ max 0 (z + |w - z|) := max_le_max (le_refl 0) h1
    have h3 : max 0 (z + |w - z|) ≤ max 0 z + |w - z| := by
      refine max_le ?_ ?_
      · linarith [le_max_left 0 z, abs_nonneg (w - z)]
      · linarith [le_max_right 0 z]
    linarith
  rw [abs_sub_le_iff]
  refine ⟨key u v, ?_⟩
  have := key v u
  rwa [abs_sub_comm] at this

private lemma configuration_sum {N : ℕ} (hN : 0 < N) (s : Fin N → S) :
    ∑ x : S, configuration s x = 1 := by
  classical
  have hcount : ∑ x : S, stateCount s x = N := by
    unfold stateCount
    rw [← Finset.card_eq_sum_card_fiberwise (f := s) (fun i _ => Finset.mem_univ (s i))]
    simp
  have hN' : ((N : ℝ)) ≠ 0 := by
    exact_mod_cast hN.ne'
  unfold configuration
  rw [← Finset.sum_div]
  rw [show ∑ x : S, (stateCount s x : ℝ) = ((∑ x : S, stateCount s x : ℕ) : ℝ) by
    rw [Nat.cast_sum], hcount]
  field_simp

private lemma per_state_estimate {N : ℕ} (hN : 0 < N)
    (ν : S → ℝ) (M : ℕ) (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (s : Fin N → S) (x : S) :
    configuration s x *
        |indexActivationProb ν M s x
          - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x|
      ≤ (Fintype.card S : ℝ) * supNorm (fun z => configuration s z - mstar z) := by
  classical
  set β := (M : ℝ) / (N : ℝ) with hβ
  set Δ := supNorm (fun z => configuration s z - mstar z) with hΔ
  have habs : ∀ z, |configuration s z - mstar z| ≤ Δ := fun z =>
    abs_le_supNorm (fun z => configuration s z - mstar z) z
  have hΔ0 : 0 ≤ Δ := le_trans (abs_nonneg _) (habs x)
  have hm0 : ∀ z, 0 ≤ configuration s z := by
    intro z
    unfold configuration
    positivity
  have hcard1 : 1 ≤ Fintype.card S := Fintype.card_pos_iff.mpr ⟨x⟩
  have hact := configuration_mul_indexActivationProb hN ν M s x
  set am := activateFraction ν β (configuration s) x with ham
  set astar := activateFraction ν β mstar x with hastar
  have ham0 : 0 ≤ am := by
    rw [ham]
    unfold activateFraction
    exact le_min (hm0 x) (le_max_left _ _)
  have hamle : am ≤ configuration s x := by
    rw [ham]; unfold activateFraction; exact min_le_left _ _
  have hastar0 : 0 ≤ astar := by
    rw [hastar]; unfold activateFraction
    exact le_min (hmstar.1 x) (le_max_left _ _)
  have hastarle : astar ≤ mstar x := by
    rw [hastar]; unfold activateFraction; exact min_le_left _ _
  -- the higher-priority masses differ by at most (|S| − 1) Δ
  have hHdiff : |higherPriorityMass ν (configuration s) x - higherPriorityMass ν mstar x|
      ≤ ((Fintype.card S : ℝ) - 1) * Δ := by
    unfold higherPriorityMass
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hsub : (Finset.univ.filter fun y => ν x < ν y) ⊆ Finset.univ.erase x := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨-, hlt⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ y⟩
      rintro rfl
      exact lt_irrefl _ hlt
    have hcardle : (((Finset.univ.filter fun y => ν x < ν y).card : ℕ) : ℝ)
        ≤ (Fintype.card S : ℝ) - 1 := by
      have h1 : (Finset.univ.filter fun y => ν x < ν y).card
          ≤ (Finset.univ.erase x).card := Finset.card_le_card hsub
      have h2 : (Finset.univ.erase x).card = Fintype.card S - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
      have h3 : (Finset.univ.filter fun y => ν x < ν y).card ≤ Fintype.card S - 1 := by
        omega
      have h4 : ((Fintype.card S - 1 : ℕ) : ℝ) = (Fintype.card S : ℝ) - 1 := by
        rw [Nat.cast_sub hcard1]; norm_num
      calc (((Finset.univ.filter fun y => ν x < ν y).card : ℕ) : ℝ)
          ≤ ((Fintype.card S - 1 : ℕ) : ℝ) := by exact_mod_cast h3
        _ = (Fintype.card S : ℝ) - 1 := h4
    calc ∑ y ∈ Finset.univ.filter fun y => ν x < ν y, |configuration s y - mstar y|
        ≤ ∑ _y ∈ Finset.univ.filter fun y => ν x < ν y, Δ :=
          Finset.sum_le_sum fun y _ => habs y
      _ = (((Finset.univ.filter fun y => ν x < ν y).card : ℕ) : ℝ) * Δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Fintype.card S : ℝ) - 1) * Δ := mul_le_mul_of_nonneg_right hcardle hΔ0
  -- the activated fractions differ by at most max(Δ, (|S|−1)Δ)
  have hadiff : |am - astar| ≤ max Δ (((Fintype.card S : ℝ) - 1) * Δ) := by
    rw [ham, hastar]
    unfold activateFraction
    refine le_trans (min_lipschitz _ _ _ _) ?_
    refine max_le_max (habs x) ?_
    refine le_trans (max_zero_lipschitz _ _) ?_
    have heq : β - higherPriorityMass ν (configuration s) x
        - (β - higherPriorityMass ν mstar x)
        = -(higherPriorityMass ν (configuration s) x - higherPriorityMass ν mstar x) := by
      ring
    rw [heq, abs_neg]
    exact hHdiff
  by_cases hcard : Fintype.card S = 1
  · -- singleton state space: the two configurations coincide and the deviation is zero
    have hsub : ∀ z : S, z = x := by
      intro z
      rcases Fintype.card_eq_one_iff.mp hcard with ⟨y, hy⟩
      rw [hy z, hy x]
    have hsingle : ∀ f : S → ℝ, ∑ z, f z = f x := by
      intro f
      exact Fintype.sum_eq_single x fun y hy => absurd (hsub y) hy
    have hcfg1 : configuration s x = 1 := by
      have := configuration_sum hN s
      rwa [hsingle] at this
    have hmstar1 : mstar x = 1 := by
      have := hmstar.2
      rwa [hsingle] at this
    have hcfgeq : configuration s = mstar := by
      funext z
      rw [hsub z, hcfg1, hmstar1]
    have hameq : am = astar := by rw [ham, hastar, hcfgeq]
    have hiap : indexActivationProb ν M s x = astar := by
      have h := hact
      rw [hcfg1, one_mul] at h
      rw [h, hameq]
    have hmf : meanFieldActivationProb ν β mstar x = astar := by
      unfold meanFieldActivationProb
      rw [if_neg (by rw [hmstar1]; norm_num), hmstar1, div_one]
    rw [hiap, hmf, sub_self, abs_zero, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hΔ0
  · -- at least two states
    have hcard2 : 2 ≤ Fintype.card S := by omega
    have hc1R : (1 : ℝ) ≤ (Fintype.card S : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (Fintype.card S : ℝ) := by exact_mod_cast hcard2
      linarith
    have hmax : max Δ (((Fintype.card S : ℝ) - 1) * Δ) = ((Fintype.card S : ℝ) - 1) * Δ := by
      refine max_eq_right ?_
      nlinarith
    rw [hmax] at hadiff
    by_cases hmx : mstar x = 0
    · -- no mean-field mass in `x`: the limiting policy idles there
      have hmf0 : meanFieldActivationProb ν β mstar x = 0 := by
        unfold meanFieldActivationProb
        rw [if_pos hmx]
      have hiap0 : 0 ≤ indexActivationProb ν M s x := by
        unfold indexActivationProb
        by_cases hc : stateCount s x = 0
        · rw [if_pos hc]
        · rw [if_neg hc]
          positivity
      have h1 : am ≤ Δ := by
        calc am ≤ configuration s x := hamle
          _ = |configuration s x - mstar x| := by
              rw [hmx, sub_zero, abs_of_nonneg (hm0 x)]
          _ ≤ Δ := habs x
      rw [hmf0, sub_zero, abs_of_nonneg hiap0, hact]
      refine le_trans h1 ?_
      exact le_mul_of_one_le_left hΔ0 (by exact_mod_cast hcard1)
    · -- mean-field mass in `x`: compare the two ratios
      have hmxpos : 0 < mstar x := lt_of_le_of_ne (hmstar.1 x) (Ne.symm hmx)
      have hmf : meanFieldActivationProb ν β mstar x = astar / mstar x := by
        unfold meanFieldActivationProb
        rw [if_neg hmx]
      have hLHS : configuration s x *
          |indexActivationProb ν M s x - meanFieldActivationProb ν β mstar x|
          = |am - configuration s x * (astar / mstar x)| := by
        rw [hmf]
        have h1 : configuration s x *
            |indexActivationProb ν M s x - astar / mstar x|
            = |configuration s x * (indexActivationProb ν M s x - astar / mstar x)| := by
          rw [abs_mul, abs_of_nonneg (hm0 x)]
        rw [h1, mul_sub, hact]
      have hsplit : am - configuration s x * (astar / mstar x)
          = (am - astar) + (astar / mstar x) * (mstar x - configuration s x) := by
        field_simp
        ring
      have hdivle : astar / mstar x ≤ 1 := (div_le_one hmxpos).mpr hastarle
      have hdiv0 : 0 ≤ astar / mstar x := div_nonneg hastar0 hmxpos.le
      rw [hLHS, hsplit]
      refine le_trans (abs_add_le _ _) ?_
      have hB : |(astar / mstar x) * (mstar x - configuration s x)| ≤ Δ := by
        rw [abs_mul, abs_of_nonneg hdiv0]
        refine le_trans (mul_le_of_le_one_left (abs_nonneg _) hdivle) ?_
        rw [abs_sub_comm]
        exact habs x
      calc |am - astar| + |(astar / mstar x) * (mstar x - configuration s x)|
          ≤ ((Fintype.card S : ℝ) - 1) * Δ + Δ := add_le_add hadiff hB
        _ = (Fintype.card S : ℝ) * Δ := by ring

/-- Lemma 2 / Lemma 8: the entanglement of an index policy is bounded by the expected
deviation of the configuration from any reference configuration `m✦`. -/
theorem solution
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (N : ℕ) (hN : 0 < N)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π)
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (hμ : IsDist μ) (hexch : IsExchangeableDist μ)
    (hstat : IsStationary (inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ)
    (i : Fin N) :
    entanglementN i μ (inducedTransition
        (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
      ≤ (Fintype.card S : ℝ) ^ 2 *
          ∑ p : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)),
            μ p * supNorm (fun x => configuration (fun j => (p j).1) x - mstar x) := by
  classical
  set M := ⌊α * (N : ℝ)⌋₊ with hMdef
  have hNR : ((N : ℝ)) ≠ 0 := by exact_mod_cast hN.ne'
  -- the local kernels of the bandit form a weakly-coupled system
  have hPl : IsLocalKernel (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool)
      (fun _ => rmabKernel P0 P1) := by
    constructor
    · intro j x a y
      cases a
      · simpa [rmabKernel] using hP0.1 x y
      · simpa [rmabKernel] using hP1.1 x y
    · intro j x a
      cases a
      · simpa [rmabKernel] using hP0.2 x
      · simpa [rmabKernel] using hP1.2 x
  have hwc : IsWeaklyCoupled
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j))
      (fun _ : Fin N => rmabKernel P0 P1) := fun _ _ _ => rfl
  -- the mean-field limiting policy at `mstar`, at the system's own activation fraction
  have hmfap01 : ∀ x : S, 0 ≤ meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x ∧
      meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x ≤ 1 := by
    intro x
    unfold meanFieldActivationProb
    by_cases hmx : mstar x = 0
    · rw [if_pos hmx]
      norm_num
    · rw [if_neg hmx]
      have hpos : 0 < mstar x := lt_of_le_of_ne (hmstar.1 x) (Ne.symm hmx)
      have h0 : 0 ≤ activateFraction ν ((M : ℝ) / (N : ℝ)) mstar x :=
        le_min (hmstar.1 x) (le_max_left _ _)
      exact ⟨div_nonneg h0 hpos.le, (div_le_one hpos).mpr (min_le_left _ _)⟩
  have hπlP : IsLocalPolicy (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool) (i := i)
      (meanFieldLocalPolicy ν ((M : ℝ) / (N : ℝ)) mstar) := by
    constructor
    · intro x a
      cases a
      · simpa [meanFieldLocalPolicy] using (by linarith [(hmfap01 x).2] :
          (0:ℝ) ≤ 1 - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x)
      · simpa [meanFieldLocalPolicy] using (hmfap01 x).1
    · intro x
      rw [Fintype.sum_bool]
      simp only [meanFieldLocalPolicy, if_true, Bool.false_eq_true, if_false]
      ring
  -- Proposition 1 with the mean-field limiting policy as witness
  have hE := prop1_nonneg
    (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j))
    (fun _ => rmabKernel P0 P1) hPl hwc π hπ.1 μ hμ.1 hstat i
    (meanFieldLocalPolicy ν ((M : ℝ) / (N : ℝ)) mstar) hπlP
  refine le_trans hE ?_
  -- with two actions the mismatch collapses to the activation-probability deviation
  have hmargsum : ∀ s : Fin N → S,
      policyMarginal (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool) i π s true
        + policyMarginal (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool) i π s false
        = 1 := by
    intro s
    have h1 : ∑ ai : Bool,
        policyMarginal (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool) i π s ai
          = 1 := by
      unfold policyMarginal
      rw [Finset.sum_comm]
      calc ∑ a : JointAction (fun _ : Fin N => Bool), ∑ ai : Bool,
            (if a i = ai then π s a else 0)
          = ∑ a : JointAction (fun _ : Fin N => Bool), π s a := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_ite_eq]
            simp
        _ = 1 := hπ.1.2 s
    rw [Fintype.sum_bool] at h1
    exact h1
  have hmm : policyMismatch i π μ (meanFieldLocalPolicy ν ((M : ℝ) / (N : ℝ)) mstar)
      = ∑ s : Fin N → S, occupancyStateMarginal μ s *
          |indexActivationProb ν M s (s i)
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i)| := by
    unfold policyMismatch
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hπlt : meanFieldLocalPolicy ν ((M : ℝ) / (N : ℝ)) mstar (s i) true
        = meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i) := by
      simp [meanFieldLocalPolicy]
    have hπlf : meanFieldLocalPolicy ν ((M : ℝ) / (N : ℝ)) mstar (s i) false
        = 1 - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i) := by
      simp [meanFieldLocalPolicy]
    have hcollapse : ∑ ai : Bool,
        |policyMarginal (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool) i π s ai
          - meanFieldLocalPolicy ν ((M : ℝ) / (N : ℝ)) mstar (s i) ai|
        = 2 * |policyMarginal (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool)
            i π s true
          - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i)| := by
      rw [Fintype.sum_bool, hπlt, hπlf]
      have hf : policyMarginal (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool)
            i π s false
          - (1 - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i))
          = -(policyMarginal (St := fun _ : Fin N => S) (Act := fun _ : Fin N => Bool)
              i π s true
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i)) := by
        have := hmargsum s
        linarith
      rw [hf, abs_neg]
      ring
    rw [hcollapse, hπ.2.2 s i]
    ring
  rw [hmm]
  -- the occupancy weights are nonnegative
  have hocc0 : ∀ s : Fin N → S, 0 ≤ occupancyStateMarginal μ s := by
    intro s
    unfold occupancyStateMarginal
    refine Finset.sum_nonneg fun p _ => ?_
    by_cases h1 : (fun j => (p j).1) = s
    · rw [if_pos h1]; exact hμ.1 p
    · rw [if_neg h1]
  -- exchangeability: the per-agent deviation equals its average over the agents
  have hAj : ∀ j : Fin N,
      (∑ s : Fin N → S, occupancyStateMarginal μ s *
          |indexActivationProb ν M s (s i)
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i)|)
        = ∑ s : Fin N → S, occupancyStateMarginal μ s *
            |indexActivationProb ν M s (s j)
              - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s j)| := by
    intro j
    have het : ∀ t : Fin N → S,
        (Equiv.piCongrLeft' (fun _ : Fin N => S) (Equiv.swap i j).symm) t
          = t ∘ (Equiv.swap i j) := by
      intro t
      funext k
      simp [Equiv.piCongrLeft']
    rw [← Equiv.sum_comp (Equiv.piCongrLeft' (fun _ : Fin N => S) (Equiv.swap i j).symm)
      (fun s => occupancyStateMarginal μ s *
        |indexActivationProb ν M s (s i)
          - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i)|)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [het t]
    have h1 : occupancyStateMarginal μ (t ∘ Equiv.swap i j) = occupancyStateMarginal μ t :=
      occupancyStateMarginal_comp_perm μ hexch t (Equiv.swap i j)
    have h2 : indexActivationProb ν M (t ∘ Equiv.swap i j) ((t ∘ Equiv.swap i j) i)
        = indexActivationProb ν M t (t j) := by
      rw [indexActivationProb_comp_perm]
      congr 1
      simp [Function.comp_apply, Equiv.swap_apply_left]
    have h3 : (t ∘ Equiv.swap i j) i = t j := by
      simp [Function.comp_apply, Equiv.swap_apply_left]
    rw [h1, h2, h3]
  have hAavg : (∑ s : Fin N → S, occupancyStateMarginal μ s *
        |indexActivationProb ν M s (s i)
          - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i)|)
      = ∑ s : Fin N → S, occupancyStateMarginal μ s *
          ∑ x : S, configuration s x *
            |indexActivationProb ν M s x
              - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x| := by
    have hsumj : (N : ℝ) * (∑ s : Fin N → S, occupancyStateMarginal μ s *
          |indexActivationProb ν M s (s i)
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i)|)
        = ∑ j : Fin N, ∑ s : Fin N → S, occupancyStateMarginal μ s *
            |indexActivationProb ν M s (s j)
              - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s j)| := by
      rw [Finset.sum_congr rfl (fun j _ => (hAj j).symm), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hswap : ∑ j : Fin N, ∑ s : Fin N → S, occupancyStateMarginal μ s *
          |indexActivationProb ν M s (s j)
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s j)|
        = ∑ s : Fin N → S, occupancyStateMarginal μ s *
            ∑ j : Fin N, |indexActivationProb ν M s (s j)
              - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s j)| := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
    have hcount : ∀ (s : Fin N → S) (x : S),
        (stateCount s x : ℝ) = (N : ℝ) * configuration s x := by
      intro s x
      unfold configuration
      field_simp
    have step : ∑ s : Fin N → S, occupancyStateMarginal μ s *
          ∑ j : Fin N, |indexActivationProb ν M s (s j)
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s j)|
        = (N : ℝ) * ∑ s : Fin N → S, occupancyStateMarginal μ s *
            ∑ x : S, configuration s x *
              |indexActivationProb ν M s x
                - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [sum_fiber s (fun x => |indexActivationProb ν M s x
        - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x|)]
      have hx : ∑ x : S, (stateCount s x : ℝ) *
            |indexActivationProb ν M s x
              - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x|
          = (N : ℝ) * ∑ x : S, configuration s x *
              |indexActivationProb ν M s x
                - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hcount s x]
        ring
      rw [hx]
      ring
    have hfinal : (N : ℝ) * (∑ s : Fin N → S, occupancyStateMarginal μ s *
          |indexActivationProb ν M s (s i)
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar (s i)|)
        = (N : ℝ) * ∑ s : Fin N → S, occupancyStateMarginal μ s *
            ∑ x : S, configuration s x *
              |indexActivationProb ν M s x
                - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x| := by
      rw [hsumj, hswap, step]
    exact mul_left_cancel₀ hNR hfinal
  rw [hAavg]
  -- the per-state estimate, summed over the states
  have hbound : ∑ s : Fin N → S, occupancyStateMarginal μ s *
        ∑ x : S, configuration s x *
          |indexActivationProb ν M s x
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x|
      ≤ ∑ s : Fin N → S, occupancyStateMarginal μ s *
          ((Fintype.card S : ℝ) ^ 2 * supNorm (fun z => configuration s z - mstar z)) := by
    refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hocc0 s)
    calc ∑ x : S, configuration s x *
          |indexActivationProb ν M s x
            - meanFieldActivationProb ν ((M : ℝ) / (N : ℝ)) mstar x|
        ≤ ∑ _x : S, (Fintype.card S : ℝ) * supNorm (fun z => configuration s z - mstar z) :=
          Finset.sum_le_sum fun x _ => per_state_estimate hN ν M mstar hmstar s x
      _ = (Fintype.card S : ℝ) ^ 2 * supNorm (fun z => configuration s z - mstar z) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  refine le_trans hbound (le_of_eq ?_)
  -- transport the occupancy sum back to a sum over `μ`
  calc ∑ s : Fin N → S, occupancyStateMarginal μ s *
        ((Fintype.card S : ℝ) ^ 2 * supNorm (fun z => configuration s z - mstar z))
      = (Fintype.card S : ℝ) ^ 2 * ∑ s : Fin N → S, occupancyStateMarginal μ s *
          supNorm (fun z => configuration s z - mstar z) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ = (Fintype.card S : ℝ) ^ 2 *
          ∑ p : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)),
            μ p * supNorm (fun x => configuration (fun j => (p j).1) x - mstar x) := by
        congr 1
        unfold occupancyStateMarginal
        calc ∑ s : Fin N → S,
              (∑ p, if (fun j => (p j).1) = s then μ p else 0) *
                supNorm (fun z => configuration s z - mstar z)
            = ∑ s : Fin N → S, ∑ p,
                (if (fun j => (p j).1) = s then
                  μ p * supNorm (fun z => configuration s z - mstar z) else 0) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun p _ => ?_
              by_cases h1 : (fun j => (p j).1) = s <;> simp [h1]
          _ = ∑ p, ∑ s : Fin N → S,
                (if (fun j => (p j).1) = s then
                  μ p * supNorm (fun z => configuration s z - mstar z) else 0) :=
              Finset.sum_comm
          _ = ∑ p, μ p * supNorm (fun x => configuration (fun j => (p j).1) x - mstar x) := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_ite_eq]
              simp

end Rmab

