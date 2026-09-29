-- Prove2me | solution 1 for MarkovEntanglement.rmab_index_policy_decomposition_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-30T23:41:22.076585+00:00
-- url     : https://prove2.me/submissions/5237d9fb-c7d1-4043-b0d9-ba9c74eb5275

import Mathlib
import Theorems.Thm_MarkovEntanglement_rmab_index_policy_entanglement_le_sqrt

open scoped BigOperators
open MarkovEntanglement

namespace MEred

/-- The Bellman fixed point of a transition matrix with rewards bounded by `rmax` is bounded
by `rmax / (1 - γ)`. -/
theorem bellman_sup_bound {ι : Type*} [Fintype ι] (hne : Nonempty ι)
    (Pl : Matrix ι ι ℝ) (hPl : IsTransitionMatrix Pl) (rf : ι → ℝ) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (Qf : ι → ℝ) (hQ : IsBellmanQ Pl rf γ Qf)
    (rmax : ℝ) (hr : ∀ u, |rf u| ≤ rmax) :
    ∀ u, |Qf u| ≤ rmax / (1 - γ) := by
  haveI := hne
  obtain ⟨u₀, -, hu₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun u => |Qf u|) Finset.univ_nonempty
  have h2 : |∑ t, Pl u₀ t * Qf t| ≤ |Qf u₀| := by
    calc |∑ t, Pl u₀ t * Qf t| ≤ ∑ t, |Pl u₀ t * Qf t| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t, Pl u₀ t * |Qf t| :=
          Finset.sum_congr rfl fun t _ => by rw [abs_mul, abs_of_nonneg (hPl.1 u₀ t)]
      _ ≤ ∑ t, Pl u₀ t * |Qf u₀| :=
          Finset.sum_le_sum fun t _ =>
            mul_le_mul_of_nonneg_left (hu₀ t (Finset.mem_univ t)) (hPl.1 u₀ t)
      _ = |Qf u₀| := by rw [← Finset.sum_mul, hPl.2 u₀, one_mul]
  have h1 : |Qf u₀| ≤ |rf u₀| + γ * |∑ t, Pl u₀ t * Qf t| := by
    rw [hQ u₀]
    calc |rf u₀ + γ * ∑ t, Pl u₀ t * Qf t| ≤ |rf u₀| + |γ * ∑ t, Pl u₀ t * Qf t| := abs_add_le _ _
      _ = |rf u₀| + γ * |∑ t, Pl u₀ t * Qf t| := by rw [abs_mul, abs_of_nonneg hγ]
  have h3 := mul_le_mul_of_nonneg_left h2 hγ
  have hb : |Qf u₀| ≤ rmax + γ * |Qf u₀| := by linarith [hr u₀]
  have hmax : |Qf u₀| ≤ rmax / (1 - γ) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - γ)]
    nlinarith
  exact fun u => le_trans (hu₀ u (Finset.mem_univ u)) hmax

/-- A stationary nonnegative weight makes the transition matrix a contraction in `μ`-norm. -/
theorem mu_contract {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) (hP : ∀ p q, 0 ≤ P p q)
    (μ : ι → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hstat : IsStationary P μ) (V : ι → ℝ) :
    ∑ p, μ p * |∑ q, P p q * V q| ≤ ∑ q, μ q * |V q| := by
  calc ∑ p, μ p * |∑ q, P p q * V q| ≤ ∑ p, μ p * ∑ q, P p q * |V q| := by
        refine Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left ?_ (hμ p)
        calc |∑ q, P p q * V q| ≤ ∑ q, |P p q * V q| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ q, P p q * |V q| :=
              Finset.sum_congr rfl fun q _ => by rw [abs_mul, abs_of_nonneg (hP p q)]
    _ = ∑ q, (∑ p, μ p * P p q) * |V q| := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ q, μ q * |V q| := Finset.sum_congr rfl fun q _ => by rw [hstat q]

variable {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Averaging a function of agent `i`'s coordinate against `μ` is the same as averaging it
against the marginal of `μ` on that coordinate. -/
theorem group_by_coord (μ : Joint S → ℝ) (i : Fin N) (g : S i → ℝ) :
    ∑ p : Joint S, μ p * g (p i) = ∑ s, marginalDist i μ s * g s := by
  unfold marginalDist
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => by simp

/-- The marginal of a nonnegative weight is nonnegative. -/
theorem marginalDist_nonneg (μ : Joint S → ℝ) (hμ : ∀ p, 0 ≤ μ p) (i : Fin N) (s : S i) :
    0 ≤ marginalDist i μ s := by
  unfold marginalDist
  exact Finset.sum_nonneg fun q _ => by by_cases h : q i = s <;> simp [h, hμ q]

/-- **Jensen step.** The true (marginalised) local transition is at least as close, in the
`μ`-weighted sense, to the joint transition's marginal as any candidate local transition is:
averaging cannot increase the distance. -/
theorem true_le_candidate (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (i : Fin N) (Ptrue Pi : Matrix (S i) (S i) ℝ)
    (htrue : IsLocalTransitionN i P μ Ptrue) (t : S i) :
    ∑ p : Joint S, μ p * |Pi (p i) t - Ptrue (p i) t|
      ≤ ∑ p : Joint S, μ p * |marginalN i P p t - Pi (p i) t| := by
  rw [group_by_coord μ i (fun s => |Pi s t - Ptrue s t|)]
  have hmd := marginalDist_nonneg μ hμ i
  calc ∑ s, marginalDist i μ s * |Pi s t - Ptrue s t|
      = ∑ s, |marginalDist i μ s * Pi s t - marginalDist i μ s * Ptrue s t| :=
        Finset.sum_congr rfl fun s _ => by rw [← mul_sub, abs_mul, abs_of_nonneg (hmd s)]
    _ ≤ ∑ s, ∑ p : Joint S, (if p i = s then μ p * |Pi (p i) t - marginalN i P p t| else 0) := by
        refine Finset.sum_le_sum fun s _ => ?_
        have e1 : marginalDist i μ s * Pi s t
            = ∑ p : Joint S, (if p i = s then μ p * Pi (p i) t else 0) := by
          unfold marginalDist
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => by by_cases h : p i = s <;> simp [h]
        have e2 : marginalDist i μ s * Ptrue s t
            = ∑ p : Joint S, (if p i = s then μ p * marginalN i P p t else 0) := by
          rw [htrue s t]
          exact Finset.sum_congr rfl fun p _ => by by_cases h : p i = s <;> simp [h]
        rw [e1, e2, ← Finset.sum_sub_distrib]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun p _ => ?_)
        by_cases h : p i = s
        · rw [if_pos h, if_pos h, if_pos h, ← mul_sub, abs_mul, abs_of_nonneg (hμ p)]
        · rw [if_neg h, if_neg h, if_neg h]
          simp
    _ = ∑ p : Joint S, μ p * |Pi (p i) t - marginalN i P p t| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => by simp
    _ = ∑ p : Joint S, μ p * |marginalN i P p t - Pi (p i) t| :=
        Finset.sum_congr rfl fun p _ => by rw [abs_sub_comm]


/-- **The true local transition is within twice the entanglement.**  The joint transition's
agent-`i` marginal deviates from the marginalised local transition by at most twice the
measure of Markov entanglement.  Only nonnegativity of the occupancy weights is used — no
strict positivity — which is what makes this applicable to the budget-constrained chains of a
restless bandit, whose stationary occupancy vanishes on every non-budgeted action profile. -/
theorem true_dev_le_two_entanglement (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (i : Fin N) (hne : Nonempty (S i))
    (Ptrue : Matrix (S i) (S i) ℝ) (htrue : IsLocalTransitionN i P μ Ptrue) :
    muAgentTVDistN i μ P Ptrue ≤ 2 * entanglementN i μ P := by
  classical
  obtain ⟨c⟩ := hne
  have hPc : IsTransitionMatrix (fun (_ : S i) (t : S i) => if t = c then (1:ℝ) else 0) := by
    constructor
    · intro a b
      by_cases h : b = c <;> simp [h]
    · intro a
      simp
  have hAne : Set.Nonempty {r : ℝ | ∃ Pi : Matrix (S i) (S i) ℝ,
      IsTransitionMatrix Pi ∧ r = muAgentTVDistN i μ P Pi} := ⟨_, _, hPc, rfl⟩
  have hhalf : ∀ f : Joint S → ℝ,
      ∑ p : Joint S, μ p * ((1/2) * f p) = (1/2) * ∑ p : Joint S, μ p * f p := by
    intro f
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hswap : ∀ f : Joint S → S i → ℝ,
      ∑ p : Joint S, μ p * ∑ t, f p t = ∑ t, ∑ p : Joint S, μ p * f p t := by
    intro f
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hkey : ∀ Pi : Matrix (S i) (S i) ℝ,
      muAgentTVDistN i μ P Ptrue ≤ 2 * muAgentTVDistN i μ P Pi := by
    intro Pi
    have step2 : ∑ p : Joint S, μ p * ∑ t, |Pi (p i) t - Ptrue (p i) t|
        ≤ ∑ p : Joint S, μ p * ∑ t, |marginalN i P p t - Pi (p i) t| := by
      rw [hswap (fun p t => |Pi (p i) t - Ptrue (p i) t|),
        hswap (fun p t => |marginalN i P p t - Pi (p i) t|)]
      exact Finset.sum_le_sum fun t _ => true_le_candidate P μ hμ i Ptrue Pi htrue t
    have step1 : ∑ p : Joint S, μ p * ∑ t, |marginalN i P p t - Ptrue (p i) t|
        ≤ (∑ p : Joint S, μ p * ∑ t, |marginalN i P p t - Pi (p i) t|)
          + ∑ p : Joint S, μ p * ∑ t, |Pi (p i) t - Ptrue (p i) t| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [← mul_add, ← Finset.sum_add_distrib]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun t _ => abs_sub_le _ _ _) (hμ p)
    unfold muAgentTVDistN
    rw [hhalf (fun p => ∑ t, |marginalN i P p t - Ptrue (p i) t|),
      hhalf (fun p => ∑ t, |marginalN i P p t - Pi (p i) t|)]
    linarith
  have hhalf2 : muAgentTVDistN i μ P Ptrue / 2 ≤ entanglementN i μ P := by
    unfold entanglementN
    refine le_csInf hAne ?_
    rintro b ⟨Pi, -, rfl⟩
    linarith [hkey Pi]
  linarith

/-- **Value decomposition error under a merely nonnegative stationary occupancy measure.**
The `μ`-weighted error of decomposing the joint `Q`-function into a sum of the agents' own
local `Q`-functions is controlled by the agents' local-transition deviations. -/
theorem decomposition_error (P : Matrix (Joint S) (Joint S) ℝ) (hP : ∀ p q, 0 ≤ P p q)
    (μ : Joint S → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hstat : IsStationary P μ)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (rmax : ℝ)
    (hSne : ∀ i, Nonempty (S i))
    (r : ∀ i, S i → ℝ) (hr : ∀ i s, |r i s| ≤ rmax)
    (Q : Joint S → ℝ) (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (Qi : ∀ i, S i → ℝ) (hQi : ∀ i, IsBellmanQ (Pl i) (r i) γ (Qi i)) :
    muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
      ≤ 2 * γ * rmax * (∑ i, muAgentTVDistN i μ P (Pl i)) / (1 - γ) ^ 2 := by
  classical
  have h1γ : (0:ℝ) < 1 - γ := by linarith
  set V : Joint S → ℝ := fun p => Q p - ∑ i, Qi i (p i) with hVdef
  set W : Joint S → ℝ := fun p => ∑ i, ∑ t, |marginalN i P p t - Pl i (p i) t| with hWdef
  set B : ℝ := rmax / (1 - γ) with hBdef
  have hB : ∀ (i : Fin N) (t : S i), |Qi i t| ≤ B := fun i =>
    bellman_sup_bound (hSne i) (Pl i) (hPl i) (r i) γ hγ hγ1 (Qi i) (hQi i) rmax (hr i)
  have hmarg : ∀ (i : Fin N) (p : Joint S),
      ∑ t, marginalN i P p t * Qi i t = ∑ q : Joint S, P p q * Qi i (q i) := by
    intro i p
    unfold marginalN
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => by simp
  have hV : ∀ p : Joint S, V p = γ * (∑ q : Joint S, P p q * V q)
      + γ * ∑ i, ∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t := by
    intro p
    have hsplit : ∑ q : Joint S, P p q * V q
        = (∑ q : Joint S, P p q * Q q) - ∑ i, ∑ t, marginalN i P p t * Qi i t := by
      simp only [hVdef]
      rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => mul_sub (P p q) (Q q) _),
        Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) => Finset.mul_sum _ _ _),
        Finset.sum_comm]
      exact (Finset.sum_congr rfl fun i _ => hmarg i p).symm
    have hQsum : ∑ i, Qi i (p i)
        = (∑ i, r i (p i)) + γ * ∑ i, ∑ t, Pl i (p i) t * Qi i t := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hQi i (p i)
    have hdiff : ∑ i, ∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t
        = (∑ i, ∑ t, marginalN i P p t * Qi i t) - ∑ i, ∑ t, Pl i (p i) t * Qi i t := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => sub_mul _ _ _
    have hQp := hQ p
    simp only [hVdef]
    rw [hsplit, hdiff, hQp, hQsum]
    ring
  have hD : ∀ p : Joint S,
      |∑ i, ∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t| ≤ B * W p := by
    intro p
    calc |∑ i, ∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t|
        ≤ ∑ i, |∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, B * ∑ t, |marginalN i P p t - Pl i (p i) t| := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc |∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t|
              ≤ ∑ t, |(marginalN i P p t - Pl i (p i) t) * Qi i t| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ t, |marginalN i P p t - Pl i (p i) t| * B := by
                refine Finset.sum_le_sum fun t _ => ?_
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_left (hB i t) (abs_nonneg _)
            _ = B * ∑ t, |marginalN i P p t - Pl i (p i) t| := by
                rw [← Finset.sum_mul]; ring
      _ = B * W p := by rw [hWdef, Finset.mul_sum]
  have hT : ∀ i : Fin N, ∑ p : Joint S, μ p * ∑ t, |marginalN i P p t - Pl i (p i) t|
      = 2 * muAgentTVDistN i μ P (Pl i) := by
    intro i
    unfold muAgentTVDistN
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hWsum : ∑ p : Joint S, μ p * W p = 2 * ∑ i, muAgentTVDistN i μ P (Pl i) := by
    have hsw : ∑ p : Joint S, μ p * W p
        = ∑ i, ∑ p : Joint S, μ p * ∑ t, |marginalN i P p t - Pl i (p i) t| := by
      simp only [hWdef, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [hsw, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hT i), ← Finset.mul_sum]
  have hstep : ∀ p : Joint S, μ p * |V p|
      ≤ μ p * (γ * |∑ q : Joint S, P p q * V q|) + γ * B * (μ p * W p) := by
    intro p
    have hin : |V p| ≤ γ * |∑ q : Joint S, P p q * V q| + γ * (B * W p) := by
      rw [hV p]
      calc |γ * (∑ q : Joint S, P p q * V q)
              + γ * ∑ i, ∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t|
          ≤ |γ * (∑ q : Joint S, P p q * V q)|
              + |γ * ∑ i, ∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t| := abs_add_le _ _
        _ = γ * |∑ q : Joint S, P p q * V q|
              + γ * |∑ i, ∑ t, (marginalN i P p t - Pl i (p i) t) * Qi i t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hγ]
        _ ≤ γ * |∑ q : Joint S, P p q * V q| + γ * (B * W p) := by
            have := mul_le_mul_of_nonneg_left (hD p) hγ
            linarith
    have := mul_le_mul_of_nonneg_left hin (hμ p)
    nlinarith [this]
  have hcontr := mu_contract P hP μ hμ hstat V
  have hsum1 : ∑ p : Joint S, μ p * (γ * |∑ q : Joint S, P p q * V q|)
      ≤ γ * ∑ p : Joint S, μ p * |V p| := by
    calc ∑ p : Joint S, μ p * (γ * |∑ q : Joint S, P p q * V q|)
        = γ * ∑ p : Joint S, μ p * |∑ q : Joint S, P p q * V q| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ γ * ∑ q : Joint S, μ q * |V q| := mul_le_mul_of_nonneg_left hcontr hγ
  have hsum2 : ∑ p : Joint S, γ * B * (μ p * W p)
      = γ * B * (2 * ∑ i, muAgentTVDistN i μ P (Pl i)) := by
    rw [← Finset.mul_sum, hWsum]
  have hfin : muNorm μ V ≤ γ * muNorm μ V + γ * B * (2 * ∑ i, muAgentTVDistN i μ P (Pl i)) := by
    unfold muNorm
    calc ∑ p : Joint S, μ p * |V p|
        ≤ ∑ p : Joint S, (μ p * (γ * |∑ q : Joint S, P p q * V q|) + γ * B * (μ p * W p)) :=
          Finset.sum_le_sum fun p _ => hstep p
      _ = (∑ p : Joint S, μ p * (γ * |∑ q : Joint S, P p q * V q|))
            + ∑ p : Joint S, γ * B * (μ p * W p) := Finset.sum_add_distrib
      _ ≤ γ * (∑ p : Joint S, μ p * |V p|)
            + γ * B * (2 * ∑ i, muAgentTVDistN i μ P (Pl i)) := by
          rw [hsum2]; linarith
  have h2 : (1 - γ) * muNorm μ V ≤ γ * B * (2 * ∑ i, muAgentTVDistN i μ P (Pl i)) := by
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 h1γ.le
  have h4 : (1 - γ) * (γ * B * (2 * ∑ i, muAgentTVDistN i μ P (Pl i)))
      = 2 * γ * rmax * (∑ i, muAgentTVDistN i μ P (Pl i)) := by
    rw [hBdef]
    field_simp
  rw [le_div_iff₀ (by positivity : (0:ℝ) < (1 - γ) ^ 2)]
  calc muNorm μ V * (1 - γ) ^ 2 = (1 - γ) * ((1 - γ) * muNorm μ V) := by ring
    _ ≤ (1 - γ) * (γ * B * (2 * ∑ i, muAgentTVDistN i μ P (Pl i))) := h3
    _ = 2 * γ * rmax * (∑ i, muAgentTVDistN i μ P (Pl i)) := h4

end MEred

open MarkovEntanglement MEred in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (hUGAP : IsUniformGlobalAttractor (meanFieldMap P0 P1 ν α) mstar)
    (hnd : IsNonDegenerateMeanField ν α mstar)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (rmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ), 0 < N →
        ∀ (π : (Fin N → S) → (Fin N → Bool) → ℝ),
          IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π →
          ∀ (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ),
            IsDist μ →
            IsExchangeableDist μ →
            IsStationary (inducedTransition
              (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ →
            ∀ (r : ∀ i : Fin N, S × Bool → ℝ), (∀ i x, |r i x| ≤ rmax) →
            ∀ (Q : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
              (Pl : ∀ i : Fin N, Matrix (S × Bool) (S × Bool) ℝ)
              (Qi : ∀ i : Fin N, S × Bool → ℝ),
              IsBellmanQ (inducedTransition
                (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
                (fun p => ∑ i, r i (p i)) γ Q →
              (∀ i, IsTransitionMatrix (Pl i)) →
              (∀ i, IsLocalTransitionN i (inducedTransition
                (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ (Pl i)) →
              (∀ i, IsBellmanQ (Pl i) (r i) γ (Qi i)) →
                muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
                  ≤ 4 * C * γ * Real.sqrt (N : ℝ) * rmax / (1 - γ) ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := MarkovEntanglement.rmab_index_policy_entanglement_le_sqrt
    P0 P1 hP0 hP1 ν hν α hα hα1 mstar hmstar hUGAP hnd
  refine ⟨C, hC0, ?_⟩
  intro N hN π hπ μ hμ hexch hstat r hr Q Pl Qi hQ hPl hlocal hQi
  have h1γ : (0:ℝ) < 1 - γ := by linarith
  have hdiv : ∀ a b c : ℝ, a ≤ b → 0 < c → a / c ≤ b / c := by
    intro a b c hab hc
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hab (le_of_lt (inv_pos.2 hc))
  -- the state-action space is inhabited, otherwise `μ` could not be a distribution
  have hne : Nonempty (Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool))) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h := hμ.2
    simp at h
  obtain ⟨p0⟩ := hne
  have hSne : ∀ i : Fin N,
      Nonempty (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool) i) := fun i => ⟨p0 i⟩
  have hrmax : 0 ≤ rmax := le_trans (abs_nonneg _) (hr ⟨0, hN⟩ (p0 ⟨0, hN⟩))
  -- the induced joint transition has nonnegative entries
  have hPnn : ∀ p q, 0 ≤ inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π p q := by
    intro p q
    refine mul_nonneg (Finset.prod_nonneg fun j _ => ?_) (hπ.1.1 _ _)
    by_cases h : (p j).2 = true <;> simp [rmabKernel, h, hP0.1, hP1.1]
  -- the decomposition error is controlled by the agents' local-transition deviations
  have hdec := decomposition_error
    (inducedTransition (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
    hPnn μ hμ.1 hstat γ hγ hγ1 rmax hSne r hr Q hQ Pl hPl Qi hQi
  -- each deviation is at most twice the entanglement, hence at most `2C/√N`
  have hTbound : ∑ i, muAgentTVDistN i μ (inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) (Pl i)
      ≤ 2 * C * Real.sqrt (N : ℝ) := by
    calc ∑ i, muAgentTVDistN i μ (inducedTransition
            (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) (Pl i)
        ≤ ∑ _i : Fin N, 2 * (C / Real.sqrt (N : ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := true_dev_le_two_entanglement
            (inducedTransition (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
            μ hμ.1 i (hSne i) (Pl i) (hlocal i)
          have h2 := hC N hN π hπ μ hμ hexch hstat i
          linarith
      _ = (N : ℝ) * (2 * (C / Real.sqrt (N : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = 2 * C * ((N : ℝ) / Real.sqrt (N : ℝ)) := by ring
      _ = 2 * C * Real.sqrt (N : ℝ) := by rw [Real.div_sqrt]
  refine le_trans hdec (hdiv _ _ _ ?_ (pow_pos h1γ 2))
  have hcoef : (0:ℝ) ≤ 2 * γ * rmax := by positivity
  calc 2 * γ * rmax * (∑ i, muAgentTVDistN i μ (inducedTransition
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) (Pl i))
      ≤ 2 * γ * rmax * (2 * C * Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hTbound hcoef
    _ = 4 * C * γ * Real.sqrt (N : ℝ) * rmax := by ring
