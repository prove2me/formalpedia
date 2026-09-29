-- Prove2me | solution 2 for KServer.randomized_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T23:59:46.936425+00:00
-- url     : https://prove2.me/submissions/f5b58cbc-6f53-4f5b-a198-f8c2c2e59c77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Theorems.Thm_KServer_randomized_yao_averaging
import Theorems.Thm_KServer_schedule_exists
import Theorems.Thm_KServer_kserver_distributional_lower_bound

namespace KServer

/-- the offline optimum is nonnegative -/
theorem offlineCost_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : 0 ≤ offlineCost C₀ σ := by
  obtain ⟨S, hS⟩ := schedule_exists k hk M C₀ σ
  refine le_csInf ⟨_, ⟨S, hS, rfl⟩⟩ ?_
  rintro x ⟨S', -, rfl⟩
  exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  where moveCost_nonneg : ∀ (C C' : Config k M), 0 ≤ moveCost C C' :=
    fun C C' => Finset.sum_nonneg fun i _ => dist_nonneg

end KServer

open KServer

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ m : MetricSpace (Fin (k + 1)),
        ∀ (C₀ : Config k (Fin (k + 1)))
          (A : @RandomizedAlgorithm k (Fin (k + 1)) m) (ρ : ℝ),
          @RandomizedAlgorithm.IsCompetitiveFrom k (Fin (k + 1)) m A C₀ ρ →
            c * Real.log k ^ 2 ≤ ρ := by
  obtain ⟨c, hc, k₀, H⟩ := KServer.kserver_distributional_lower_bound
  refine ⟨c, hc, max k₀ 2, fun k hk => ?_⟩
  have hk₀ : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨m, Hm⟩ := H k hk₀
  refine ⟨m, ?_⟩
  letI := m
  intro C₀ A ρ hA
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk2
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  set L : ℝ := c * Real.log (k : ℝ) ^ 2 with hL
  have hLpos : 0 < L := by
    have : 0 < Real.log (k : ℝ) ^ 2 := by positivity
    simpa [hL] using mul_pos hc this
  by_contra hcon
  push_neg at hcon
  -- replace ρ by its nonnegative part
  set ρ' : ℝ := max ρ 0 with hρ'
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  have hρρ' : ρ ≤ ρ' := le_max_left _ _
  have hρ'L : ρ' < L := max_lt hcon hLpos
  have hk1' : 1 ≤ k := by omega
  have hcomp' : A.IsCompetitiveFrom C₀ ρ' := by
    obtain ⟨hconf, a, ha⟩ := hA
    refine ⟨hconf, a, fun σ => ?_⟩
    refine le_trans (ha σ) (ENNReal.ofReal_le_ofReal ?_)
    have hopt : 0 ≤ offlineCost C₀ σ :=
      KServer.offlineCost_nonneg k hk1' (Fin (k + 1)) C₀ σ
    nlinarith [mul_le_mul_of_nonneg_right hρρ' hopt]
  obtain ⟨a, ha0, hYao⟩ :=
    KServer.randomized_yao_averaging k (Fin (k + 1)) A C₀ ρ' hρ'0 hcomp'
  set N : ℝ := (a + 1) / (L - ρ') + 1 with hN
  obtain ⟨n, p, σ, hp0, hp1, hNle, hlow⟩ := Hm C₀ N
  obtain ⟨i, hconfi, hYaoi⟩ := hYao n p hp0 hp1 σ 1 one_pos
  set S : ℝ := ∑ j, p j * offlineCost C₀ (σ j) with hS
  have hchild := hlow (A.alg i) hconfi
  have hgap : 0 < L - ρ' := by linarith
  have hkey : (L - ρ') * S ≤ a + 1 := by nlinarith [hchild, hYaoi]
  have hNS : N ≤ S := hNle
  have hne : L - ρ' ≠ 0 := ne_of_gt hgap
  have hdiv : (L - ρ') * ((a + 1) / (L - ρ')) = a + 1 := by
    field_simp
  have hexp : (L - ρ') * N = a + 1 + (L - ρ') := by
    rw [hN, mul_add, mul_one, hdiv]
  nlinarith [mul_le_mul_of_nonneg_left hNS (le_of_lt hgap)]
