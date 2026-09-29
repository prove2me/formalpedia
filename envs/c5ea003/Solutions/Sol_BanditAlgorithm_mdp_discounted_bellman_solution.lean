-- Prove2me | solution 1 for BanditAlgorithm.mdp_discounted_bellman_solution
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T15:09:47.442532+00:00
-- url     : https://prove2.me/submissions/ddd53198-bc03-4bd9-a31c-7d6cfef6fde2

import Definitions.Def_FiniteMDPLearning
import Mathlib.Topology.MetricSpace.Contracting

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

/-!
For a discount factor `γ ∈ [0,1)` the Bellman optimality operator
`(T v)(s) = max_a (r_a(s) + γ ⟨P_a(s), v⟩)` is a `γ`-contraction of `Fin S → ℝ`
in the supremum norm, so it has a fixed point: the discounted value function.
The maximising action defines the greedy policy.
-/

variable {S A : ℕ}

/-- The transition rows of an MDP sum to one, read in `ℝ`. -/
private lemma rowSumOne (M : FiniteMDP S A) (s : Fin S) (a : Fin A) :
    ∑ s', (M.P s a s' : ℝ) = 1 := by
  rw [← NNReal.coe_sum, M.P_sum_one]
  norm_num

/-- An average against a transition row is at most any upper bound of the
integrand. -/
private lemma rowMulLe (M : FiniteMDP S A) (s : Fin S) (a : Fin A) {u : Fin S → ℝ} {c : ℝ}
    (h : ∀ s', u s' ≤ c) : ∑ s', (M.P s a s' : ℝ) * u s' ≤ c := by
  calc ∑ s', (M.P s a s' : ℝ) * u s'
      ≤ ∑ s', (M.P s a s' : ℝ) * c :=
        Finset.sum_le_sum fun s' _ ↦
          mul_le_mul_of_nonneg_left (h s') (M.P s a s').coe_nonneg
    _ = c := by rw [← Finset.sum_mul, rowSumOne, one_mul]

/-- An average against a transition row is at least any lower bound of the
integrand. -/
private lemma leRowMul (M : FiniteMDP S A) (s : Fin S) (a : Fin A) {u : Fin S → ℝ} {c : ℝ}
    (h : ∀ s', c ≤ u s') : c ≤ ∑ s', (M.P s a s' : ℝ) * u s' := by
  calc c = ∑ s', (M.P s a s' : ℝ) * c := by rw [← Finset.sum_mul, rowSumOne, one_mul]
    _ ≤ ∑ s', (M.P s a s' : ℝ) * u s' :=
        Finset.sum_le_sum fun s' _ ↦
          mul_le_mul_of_nonneg_left (h s') (M.P s a s').coe_nonneg

/-- Recentring a value function shifts the averages against transition rows by
the same constant. -/
private lemma rowMulSubConst (M : FiniteMDP S A) (s : Fin S) (a : Fin A)
    (u : Fin S → ℝ) (c : ℝ) :
    ∑ s', (M.P s a s' : ℝ) * (u s' - c) = (∑ s', (M.P s a s' : ℝ) * u s') - c := by
  have h : ∑ s', (M.P s a s' : ℝ) * (u s' - c)
      = (∑ s', (M.P s a s' : ℝ) * u s') - ∑ s', (M.P s a s' : ℝ) * c := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ ↦ by ring
  rw [h, ← Finset.sum_mul, rowSumOne, one_mul]

/-- The discounted Bellman optimality operator
`(T v)(s) = max_a (r_a(s) + γ ⟨P_a(s), v⟩)`. -/
private noncomputable def bellOp (M : FiniteMDP S A)
    (hne : (univ : Finset (Fin A)).Nonempty) (γ : ℝ) (v : Fin S → ℝ) : Fin S → ℝ :=
  fun s ↦ univ.sup' hne fun a ↦ M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * v s'

/-- The Bellman operator is a `γ`-contraction in the supremum norm. -/
private lemma bellmanOp_dist_le (M : FiniteMDP S A) (hne : (univ : Finset (Fin A)).Nonempty)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (u v : Fin S → ℝ) :
    dist (bellOp M hne γ u) (bellOp M hne γ v) ≤ γ * dist u v := by
  have step : ∀ u v : Fin S → ℝ, ∀ s : Fin S,
      bellOp M hne γ u s ≤ bellOp M hne γ v s + γ * dist u v := by
    intro u v s
    refine Finset.sup'_le hne _ fun a _ ↦ ?_
    have hcoord : ∀ s', u s' - v s' ≤ dist u v := fun s' ↦ by
      have h := dist_le_pi_dist u v s'
      rw [Real.dist_eq] at h
      exact le_trans (le_abs_self _) h
    have hsplit : ∑ s', (M.P s a s' : ℝ) * (u s' - v s')
        = (∑ s', (M.P s a s' : ℝ) * u s') - ∑ s', (M.P s a s' : ℝ) * v s' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s' _ ↦ by ring
    have hsum : (∑ s', (M.P s a s' : ℝ) * u s') - ∑ s', (M.P s a s' : ℝ) * v s' ≤ dist u v := by
      rw [← hsplit]; exact rowMulLe M s a hcoord
    have hle : M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * u s'
        ≤ (M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * v s') + γ * dist u v := by
      nlinarith
    have hsup : M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * v s' ≤ bellOp M hne γ v s :=
      Finset.le_sup' (fun a ↦ M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * v s') (mem_univ a)
    linarith
  rw [dist_pi_le_iff (by positivity)]
  intro s
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1 := step u v s
  have h2 := step v u s
  rw [dist_comm v u] at h2
  exact ⟨by linarith, by linarith⟩

/-- **Existence of the discounted value function and of a greedy policy**
(L&S §38.2; the fixed point of the discounted Bellman optimality operator).
For every discount factor `γ ∈ [0,1)` there is a `V : Fin S → ℝ` taking values
in `[0, 1/(1-γ)]` which dominates every action,
`r_a(s) + γ ⟨P_a(s), V⟩ ≤ V(s)`, with equality for the action `f(s)` of a
deterministic memoryless policy `f`. -/
theorem solution {S A : ℕ} (hS : 0 < S) (hA : 0 < A) (M : FiniteMDP S A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ (V : Fin S → ℝ) (f : Fin S → Fin A),
      (∀ s, V s ∈ Set.Icc (0 : ℝ) (1 / (1 - γ))) ∧
      (∀ s a, M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * V s' ≤ V s) ∧
      (∀ s, V s = M.r s (f s) + γ * ∑ s', (M.P s (f s) s' : ℝ) * V s') := by
  haveI : Nonempty (Fin A) := Fin.pos_iff_nonempty.mp hA
  haveI : Nonempty (Fin S) := Fin.pos_iff_nonempty.mp hS
  have hne : (univ : Finset (Fin A)).Nonempty := univ_nonempty
  have hcoe : ((Real.toNNReal γ : ℝ≥0) : ℝ) = γ := Real.coe_toNNReal γ hγ0
  have hlip : LipschitzWith (Real.toNNReal γ) (bellOp M hne γ) :=
    LipschitzWith.of_dist_le_mul fun u v ↦ by
      rw [hcoe]; exact bellmanOp_dist_le M hne hγ0 u v
  have hK : Real.toNNReal γ < 1 := by
    rw [← NNReal.coe_lt_coe, hcoe, NNReal.coe_one]; exact hγ1
  have hc : ContractingWith (Real.toNNReal γ) (bellOp M hne γ) := ⟨hK, hlip⟩
  set V := hc.fixedPoint with hVdef
  have hV : bellOp M hne γ V = V := hc.fixedPoint_isFixedPt
  have hVsup : ∀ s, V s = univ.sup' hne fun a ↦ M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * V s' :=
    fun s ↦ (congrFun hV s).symm
  have hVle : ∀ s a, M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * V s' ≤ V s := by
    intro s a
    rw [hVsup s]
    exact Finset.le_sup' (fun a ↦ M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * V s') (mem_univ a)
  have hgreedy : ∀ s, ∃ a, V s = M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * V s' := by
    intro s
    obtain ⟨a, -, ha⟩ :=
      Finset.exists_mem_eq_sup' hne fun a ↦ M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * V s'
    exact ⟨a, by rw [hVsup s, ha]⟩
  choose f hf using hgreedy
  obtain ⟨smax, hsmax⟩ := Finite.exists_max V
  obtain ⟨smin, hsmin⟩ := Finite.exists_min V
  have hγpos : 0 < 1 - γ := by linarith
  have hub : V smax ≤ 1 / (1 - γ) := by
    have h1 := hf smax
    have h2 : ∑ s', (M.P smax (f smax) s' : ℝ) * V s' ≤ V smax :=
      rowMulLe M smax (f smax) hsmax
    have h3 : M.r smax (f smax) ≤ 1 := (M.r_mem_Icc _ _).2
    rw [le_div_iff₀ hγpos]
    nlinarith
  have hlb : 0 ≤ V smin := by
    have h1 := hf smin
    have h2 : V smin ≤ ∑ s', (M.P smin (f smin) s' : ℝ) * V s' :=
      leRowMul M smin (f smin) hsmin
    have h3 : 0 ≤ M.r smin (f smin) := (M.r_mem_Icc _ _).1
    nlinarith
  exact ⟨V, f, fun s ↦ ⟨hlb.trans (hsmin s), (hsmax s).trans hub⟩, hVle, hf⟩

