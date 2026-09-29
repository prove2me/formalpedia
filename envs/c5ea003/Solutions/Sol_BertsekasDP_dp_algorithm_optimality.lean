-- Prove2me | solution 1 for BertsekasDP.dp_algorithm_optimality
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T21:28:28.8052+00:00
-- url     : https://prove2.me/submissions/8c34cd29-4599-4188-8082-1032be9a5c80

import Mathlib
import Definitions.Def_BertsekasDPModel

/-- Bertsekas, *Dynamic Programming and Optimal Control* Vol. I, Proposition 1.3.1:
the DP algorithm computes the optimal expected cost, attained by the policy that
minimizes stage by stage in the recursion. -/
theorem solution {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W) (x₀ : S) :
    IsLeast {c : ℝ | ∃ π : ℕ → S → C, (∀ k x, π k x ∈ M.U k x) ∧
        c = BertsekasDPPolicyCost M π M.N x₀}
      (BertsekasDPValue M M.N x₀) := by
  classical
  -- Lower bound: every admissible policy has expected cost at least the DP value.
  have lower : ∀ (π : ℕ → S → C), (∀ k x, π k x ∈ M.U k x) →
      ∀ m x, BertsekasDPValue M m x ≤ BertsekasDPPolicyCost M π m x := by
    intro π hπ m
    induction m with
    | zero => intro x; simp [BertsekasDPValue, BertsekasDPPolicyCost]
    | succ m ih =>
      intro x
      simp only [BertsekasDPValue, BertsekasDPPolicyCost]
      refine (Finset.inf'_le _ (hπ _ x)).trans ?_
      refine Finset.sum_le_sum fun w _ => ?_
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (ih _))
        (M.hp_nonneg _ x _ (hπ _ x) w)
  -- Optimal policy: at stage `k` pick a minimizer of the expected stage cost plus
  -- DP cost-to-go with `N - 1 - k` stages to go.
  have hchoose : ∀ k x, ∃ u ∈ M.U k x,
      (M.U k x).inf' (M.hU k x) (fun u => ∑ w, M.p k x u w *
        (M.g k x u w + BertsekasDPValue M (M.N - 1 - k) (M.f k x u w))) =
      ∑ w, M.p k x u w * (M.g k x u w + BertsekasDPValue M (M.N - 1 - k) (M.f k x u w)) :=
    fun k x => Finset.exists_mem_eq_inf' (M.hU k x) _
  choose πopt hπopt_mem hπopt_eq using hchoose
  have opt : ∀ m, m ≤ M.N → ∀ x,
      BertsekasDPPolicyCost M πopt m x = BertsekasDPValue M m x := by
    intro m
    induction m with
    | zero => intro _ x; simp [BertsekasDPValue, BertsekasDPPolicyCost]
    | succ m ih =>
      intro hm x
      have hk : M.N - 1 - (M.N - (m + 1)) = m := by omega
      have hmin := hπopt_eq (M.N - (m + 1)) x
      rw [hk] at hmin
      simp only [BertsekasDPValue, BertsekasDPPolicyCost]
      rw [hmin]
      simp only [ih (by omega : m ≤ M.N)]
  refine ⟨⟨πopt, hπopt_mem, (opt M.N le_rfl x₀).symm⟩, ?_⟩
  rintro c ⟨π, hπ, rfl⟩
  exact lower π hπ M.N x₀
