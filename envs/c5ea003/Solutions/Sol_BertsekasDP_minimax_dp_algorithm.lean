-- Prove2me | solution 1 for BertsekasDP.minimax_dp_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T21:25:36.060769+00:00
-- url     : https://prove2.me/submissions/5d389e37-2662-48e8-8546-f22f91738271

import Mathlib
import Definitions.Def_BertsekasMinimaxDPModel

/-- Bertsekas, *Dynamic Programming and Optimal Control* Vol. I, §1.6, Eqs. (1.21)–(1.24):
the minimax DP recursion computes the optimal worst-case cost, attained by the policy
that minimizes stage by stage in the recursion. -/
theorem solution {S C W : Type}
    (M : BertsekasMinimaxDPModel S C W) (x₀ : S) :
    IsLeast {c : ℝ | ∃ π : ℕ → S → C, (∀ k x, π k x ∈ M.U k x) ∧
        c = BertsekasMinimaxPolicyCost M π M.N x₀}
      (BertsekasMinimaxValue M M.N x₀) := by
  classical
  -- Lower bound: every admissible policy has worst-case cost at least the DP value.
  have lower : ∀ (π : ℕ → S → C), (∀ k x, π k x ∈ M.U k x) →
      ∀ m x, BertsekasMinimaxValue M m x ≤ BertsekasMinimaxPolicyCost M π m x := by
    intro π hπ m
    induction m with
    | zero => intro x; simp [BertsekasMinimaxValue, BertsekasMinimaxPolicyCost]
    | succ m ih =>
      intro x
      simp only [BertsekasMinimaxValue, BertsekasMinimaxPolicyCost]
      refine (Finset.inf'_le _ (hπ _ x)).trans ?_
      refine Finset.sup'_le _ _ fun w hw => ?_
      exact le_trans (add_le_add le_rfl (ih _))
        (Finset.le_sup' (fun w => M.g (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w +
          BertsekasMinimaxPolicyCost M π m (M.f (M.N - (m + 1)) x (π (M.N - (m + 1)) x) w)) hw)
  -- Optimal policy: at stage `k` pick a minimizer of the stage functional
  -- (worst-case one-step cost plus DP cost-to-go) with `N - 1 - k` stages to go.
  have hchoose : ∀ k x, ∃ u ∈ M.U k x,
      (M.U k x).inf' (M.hU k x) (fun u => (M.Wset k x u).sup' (M.hW k x u) fun w =>
        M.g k x u w + BertsekasMinimaxValue M (M.N - 1 - k) (M.f k x u w)) =
      (M.Wset k x u).sup' (M.hW k x u) fun w =>
        M.g k x u w + BertsekasMinimaxValue M (M.N - 1 - k) (M.f k x u w) :=
    fun k x => Finset.exists_mem_eq_inf' (M.hU k x) _
  choose πopt hπopt_mem hπopt_eq using hchoose
  have opt : ∀ m, m ≤ M.N → ∀ x,
      BertsekasMinimaxPolicyCost M πopt m x = BertsekasMinimaxValue M m x := by
    intro m
    induction m with
    | zero => intro _ x; simp [BertsekasMinimaxValue, BertsekasMinimaxPolicyCost]
    | succ m ih =>
      intro hm x
      have hk : M.N - 1 - (M.N - (m + 1)) = m := by omega
      have hmin := hπopt_eq (M.N - (m + 1)) x
      rw [hk] at hmin
      simp only [BertsekasMinimaxValue, BertsekasMinimaxPolicyCost]
      rw [hmin]
      simp only [ih (by omega : m ≤ M.N)]
  refine ⟨⟨πopt, hπopt_mem, (opt M.N le_rfl x₀).symm⟩, ?_⟩
  rintro c ⟨π, hπ, rfl⟩
  exact lower π hπ M.N x₀
