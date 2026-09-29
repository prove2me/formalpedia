-- Prove2me | solution 1 for BanditAlgorithm.mdp_exists_bellman_optimality_solution
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T15:14:29.518416+00:00
-- url     : https://prove2.me/submissions/94715359-ae98-4c5f-8215-2e48fe01e327

import Theorems.Thm_BanditAlgorithm_mdp_discounted_bellman_solution
import Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_ge_of_reverse_bellman_ineq
import Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_le_of_bellman_ineq
import Theorems.Thm_BanditAlgorithm_mdp_span_le_gain_mul_diameter
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

/-!
The vanishing-discount argument.  For each `γ < 1` the discounted value
function `V_γ` solves `V_γ(s) = max_a (r_a(s) + γ ⟨P_a(s), V_γ⟩)`; setting
`ρ_γ = (1-γ) max_s V_γ(s)` the pair `(ρ_γ, V_γ)` solves the *average-reward*
Bellman inequality, so the span of `V_γ` is at most `ρ_γ D(M) ≤ D(M)`,
uniformly in `γ`.  The recentred functions therefore live in the compact cube
`[-D, D]^S` and the greedy actions in a finite set, so a subsequence converges
with a constant greedy policy; in the limit the inequality becomes an equality.
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

/-- **The average-reward Bellman optimality equation has a solution**
(L&S Theorem 38.2).  For a finite MDP of finite diameter there are a gain
`ρ ∈ [0,1]`, a value function `v` of span at most `ρ D(M)`, and a deterministic
memoryless policy `f` with

`ρ + v(s) = r_{f(s)}(s) + ⟨P_{f(s)}(s), v⟩ = max_a (r_a(s) + ⟨P_a(s), v⟩)`,

and `ρ` is the optimal gain `ρ*` of the MDP. -/
theorem solution {S A : ℕ} (hS : 0 < S) (hA : 0 < A)
    (M : FiniteMDP S A) (hD : mdpDiameterENN M ≠ ⊤) :
    ∃ (ρ : ℝ) (v : Fin S → ℝ) (f : Fin S → Fin A),
      0 ≤ ρ ∧ ρ ≤ 1 ∧
      (∀ s s', v s - v s' ≤ ρ * mdpDiameter M) ∧
      (∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) ∧
      (∀ s, ρ + v s = M.r s (f s) + ∑ s', (M.P s (f s) s' : ℝ) * v s') ∧
      mdpOptimalGain M = ρ := by
  haveI : Nonempty (Fin S) := Fin.pos_iff_nonempty.mp hS
  have hD0 : (0 : ℝ) ≤ mdpDiameter M := ENNReal.toReal_nonneg
  -- the discount factors `γ k = 1 - 1/(k+1)`
  obtain ⟨γ, hγ⟩ : ∃ γ : ℕ → ℝ, ∀ k, γ k = 1 - 1 / ((k : ℝ) + 1) :=
    ⟨fun k ↦ 1 - 1 / ((k : ℝ) + 1), fun _ ↦ rfl⟩
  have hkpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k ↦ by positivity
  have hone : ∀ k, 1 - γ k = 1 / ((k : ℝ) + 1) := fun k ↦ by rw [hγ]; ring
  have hγ1 : ∀ k, γ k < 1 := by
    intro k
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [hγ]; linarith
  have hγ0 : ∀ k, 0 ≤ γ k := by
    intro k
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (hkpos k)]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [hγ]; linarith
  have hγpos : ∀ k, (0 : ℝ) < 1 - γ k := fun k ↦ by linarith [hγ1 k]
  -- the discounted value functions and their greedy policies
  choose V f hVbox hVle hVeq using fun k ↦
    BanditAlgorithm.mdp_discounted_bellman_solution hS hA M (γ k) (hγ0 k) (hγ1 k)
  choose smax hsmax using fun k ↦ Finite.exists_max (V k)
  choose smin hsmin using fun k ↦ Finite.exists_min (V k)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℕ → ℝ, ∀ k, ρ' k = (1 - γ k) * V k (smax k) :=
    ⟨fun k ↦ (1 - γ k) * V k (smax k), fun _ ↦ rfl⟩
  have hρ0 : ∀ k, 0 ≤ ρ' k := by
    intro k; rw [hρ']; exact mul_nonneg (le_of_lt (hγpos k)) (hVbox k (smax k)).1
  have hρ1 : ∀ k, ρ' k ≤ 1 := by
    intro k
    have h1 : V k (smax k) ≤ 1 / (1 - γ k) := (hVbox k _).2
    have h3 : (1 - γ k) * V k (smax k) ≤ (1 - γ k) * (1 / (1 - γ k)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt (hγpos k))
    have h4 : (1 - γ k) * (1 / (1 - γ k)) = 1 := by
      field_simp
      exact div_self (ne_of_gt (hγpos k))
    rw [hρ']; linarith
  -- `(ρ' k, V k)` solves the average-reward Bellman inequality
  have hAvg : ∀ k s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * V k s' ≤ ρ' k + V k s := by
    intro k s a
    have h1 := hVle k s a
    have h2 : ∑ s', (M.P s a s' : ℝ) * V k s' ≤ V k (smax k) :=
      rowMulLe M s a (hsmax k)
    have h3 : (0 : ℝ) ≤ 1 - γ k := le_of_lt (hγpos k)
    rw [hρ']
    nlinarith [mul_nonneg h3 (sub_nonneg.mpr h2)]
  -- hence the span of `V k` is uniformly bounded by the diameter
  have hspan : ∀ k s s', V k s - V k s' ≤ ρ' k * mdpDiameter M := fun k s s' ↦
    BanditAlgorithm.mdp_span_le_gain_mul_diameter M (ρ' k) (hρ0 k) (V k) 0 (1 / (1 - γ k))
      (hVbox k) (hAvg k) hD s s'
  have hρD : ∀ k, ρ' k * mdpDiameter M ≤ mdpDiameter M := by
    intro k
    nlinarith [hρ0 k, hρ1 k, hD0]
  -- recentre
  obtain ⟨s₀⟩ : Nonempty (Fin S) := inferInstance
  obtain ⟨w, hw⟩ : ∃ w : ℕ → Fin S → ℝ, ∀ k s, w k s = V k s - V k s₀ :=
    ⟨fun k s ↦ V k s - V k s₀, fun _ _ ↦ rfl⟩
  have hwbox : ∀ k s, w k s ∈ Set.Icc (-mdpDiameter M) (mdpDiameter M) := by
    intro k s
    have h1 := hspan k s₀ s
    have h2 := hspan k s s₀
    have h3 := hρD k
    rw [hw]
    exact ⟨by linarith, by linarith⟩
  have hwbell : ∀ k s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * w k s' ≤ ρ' k + w k s := by
    intro k s a
    have hshift : ∑ s', (M.P s a s' : ℝ) * w k s'
        = (∑ s', (M.P s a s' : ℝ) * V k s') - V k s₀ := by
      simp only [hw]
      exact rowMulSubConst M s a (V k) (V k s₀)
    have h := hAvg k s a
    rw [hshift, hw]
    linarith
  -- the greedy equality holds up to an error tending to zero
  have heps : ∀ k s,
      0 ≤ ρ' k + w k s - (M.r s (f k s) + ∑ s', (M.P s (f k s) s' : ℝ) * w k s') ∧
      ρ' k + w k s - (M.r s (f k s) + ∑ s', (M.P s (f k s) s' : ℝ) * w k s')
        ≤ (1 - γ k) * mdpDiameter M := by
    intro k s
    have hshift : ∑ s', (M.P s (f k s) s' : ℝ) * w k s'
        = (∑ s', (M.P s (f k s) s' : ℝ) * V k s') - V k s₀ := by
      simp only [hw]
      exact rowMulSubConst M s (f k s) (V k) (V k s₀)
    have hEmax : ∑ s', (M.P s (f k s) s' : ℝ) * V k s' ≤ V k (smax k) :=
      rowMulLe M s (f k s) (hsmax k)
    have hEmin : V k (smin k) ≤ ∑ s', (M.P s (f k s) s' : ℝ) * V k s' :=
      leRowMul M s (f k s) (hsmin k)
    have hsp := hspan k (smax k) (smin k)
    have hρDk := hρD k
    have hg : (0 : ℝ) ≤ 1 - γ k := le_of_lt (hγpos k)
    have heq := hVeq k s
    have hMxE0 : 0 ≤ V k (smax k) - ∑ s', (M.P s (f k s) s' : ℝ) * V k s' := by linarith
    have hMxE : V k (smax k) - (∑ s', (M.P s (f k s) s' : ℝ) * V k s') ≤ mdpDiameter M := by
      linarith
    rw [hshift, hw, hρ']
    constructor
    · nlinarith [mul_nonneg hg hMxE0]
    · nlinarith [mul_le_mul_of_nonneg_left hMxE hg]
  -- a greedy policy that recurs infinitely often
  have hfreq : ∃ g : Fin S → Fin A, ∃ᶠ k in Filter.atTop, f k = g := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ᶠ k in Filter.atTop, ∀ g : Fin S → Fin A, f k ≠ g := by
      rw [Filter.eventually_all]
      intro g
      simpa [Filter.not_frequently] using hcon g
    obtain ⟨k, hk⟩ := hall.exists
    exact hk (f k) rfl
  obtain ⟨g, hgfreq⟩ := hfreq
  obtain ⟨ψ, hψmono, hψ⟩ := Filter.extraction_of_frequently_atTop hgfreq
  -- extract a convergent subsequence from the compact cube
  have hKcompact : IsCompact
      ((Set.univ.pi fun _ : Fin S ↦ Set.Icc (-mdpDiameter M) (mdpDiameter M)) ×ˢ
        Set.Icc (0 : ℝ) 1) :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).prod isCompact_Icc
  have hmem : ∀ j : ℕ, (w (ψ j), ρ' (ψ j)) ∈
      ((Set.univ.pi fun _ : Fin S ↦ Set.Icc (-mdpDiameter M) (mdpDiameter M)) ×ˢ
        Set.Icc (0 : ℝ) 1) := fun j ↦
    ⟨fun s _ ↦ hwbox (ψ j) s, ⟨hρ0 _, hρ1 _⟩⟩
  obtain ⟨⟨v, ρ⟩, hlimmem, φ, hφmono, htend⟩ := hKcompact.tendsto_subseq hmem
  have htendw : Filter.Tendsto (fun j ↦ w (ψ (φ j))) Filter.atTop (nhds v) := by
    have h := (continuous_fst.tendsto ((v : Fin S → ℝ), ρ)).comp htend
    simpa [Function.comp] using h
  have htendρ : Filter.Tendsto (fun j ↦ ρ' (ψ (φ j))) Filter.atTop (nhds ρ) := by
    have h := (continuous_snd.tendsto ((v : Fin S → ℝ), ρ)).comp htend
    simpa [Function.comp] using h
  have htw : ∀ s, Filter.Tendsto (fun j ↦ w (ψ (φ j)) s) Filter.atTop (nhds (v s)) :=
    fun s ↦ (tendsto_pi_nhds.mp htendw) s
  have hσmono : StrictMono (fun j ↦ ψ (φ j)) := hψmono.comp hφmono
  have hfσ : ∀ j, f (ψ (φ j)) = g := fun j ↦ hψ (φ j)
  have hvbox : ∀ s, v s ∈ Set.Icc (-mdpDiameter M) (mdpDiameter M) :=
    fun s ↦ hlimmem.1 s (Set.mem_univ s)
  -- pass the Bellman inequality to the limit
  have hvbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s := by
    intro s a
    have hL : Filter.Tendsto
        (fun j ↦ M.r s a + ∑ s', (M.P s a s' : ℝ) * w (ψ (φ j)) s') Filter.atTop
        (nhds (M.r s a + ∑ s', (M.P s a s' : ℝ) * v s')) :=
      tendsto_const_nhds.add
        (tendsto_finset_sum _ fun s' _ ↦ tendsto_const_nhds.mul (htw s'))
    have hR : Filter.Tendsto (fun j ↦ ρ' (ψ (φ j)) + w (ψ (φ j)) s) Filter.atTop
        (nhds (ρ + v s)) := htendρ.add (htw s)
    exact le_of_tendsto_of_tendsto' hL hR fun j ↦ hwbell _ s a
  -- the error term vanishes along the subsequence
  have hγlim : Filter.Tendsto (fun k : ℕ ↦ (1 - γ k) * mdpDiameter M) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) * mdpDiameter M) Filter.atTop
        (nhds (0 * mdpDiameter M)) := h1.mul tendsto_const_nhds
    simp only [hone]
    simpa using h2
  have hγlimσ : Filter.Tendsto (fun j ↦ (1 - γ (ψ (φ j))) * mdpDiameter M) Filter.atTop
      (nhds 0) := hγlim.comp hσmono.tendsto_atTop
  -- pass the greedy equality to the limit
  have hveq : ∀ s, ρ + v s = M.r s (g s) + ∑ s', (M.P s (g s) s' : ℝ) * v s' := by
    intro s
    have hL : Filter.Tendsto
        (fun j ↦ M.r s (g s) + ∑ s', (M.P s (g s) s' : ℝ) * w (ψ (φ j)) s') Filter.atTop
        (nhds (M.r s (g s) + ∑ s', (M.P s (g s) s' : ℝ) * v s')) :=
      tendsto_const_nhds.add
        (tendsto_finset_sum _ fun s' _ ↦ tendsto_const_nhds.mul (htw s'))
    have hR : Filter.Tendsto (fun j ↦ ρ' (ψ (φ j)) + w (ψ (φ j)) s) Filter.atTop
        (nhds (ρ + v s)) := htendρ.add (htw s)
    refine le_antisymm ?_ ?_
    · have hL' : Filter.Tendsto
          (fun j ↦ (M.r s (g s) + ∑ s', (M.P s (g s) s' : ℝ) * w (ψ (φ j)) s')
            + (1 - γ (ψ (φ j))) * mdpDiameter M) Filter.atTop
          (nhds (M.r s (g s) + ∑ s', (M.P s (g s) s' : ℝ) * v s')) := by
        simpa using hL.add hγlimσ
      refine le_of_tendsto_of_tendsto' hR hL' fun j ↦ ?_
      have h := (heps (ψ (φ j)) s).2
      rw [hfσ j] at h
      linarith
    · refine le_of_tendsto_of_tendsto' hL hR fun j ↦ ?_
      have h := (heps (ψ (φ j)) s).1
      rw [hfσ j] at h
      linarith
  -- the span bound passes to the limit
  have hvspan : ∀ s s', v s - v s' ≤ ρ * mdpDiameter M := by
    intro s s'
    have hL : Filter.Tendsto (fun j ↦ w (ψ (φ j)) s - w (ψ (φ j)) s') Filter.atTop
        (nhds (v s - v s')) := (htw s).sub (htw s')
    have hR : Filter.Tendsto (fun j ↦ ρ' (ψ (φ j)) * mdpDiameter M) Filter.atTop
        (nhds (ρ * mdpDiameter M)) := htendρ.mul tendsto_const_nhds
    refine le_of_tendsto_of_tendsto' hL hR fun j ↦ ?_
    have h := hspan (ψ (φ j)) s s'
    rw [hw, hw]
    linarith
  -- identify `ρ` with the optimal gain
  have hle : mdpOptimalGain M ≤ ρ :=
    BanditAlgorithm.mdp_optimal_gain_le_of_bellman_ineq hS hA M ρ v (-mdpDiameter M) (mdpDiameter M) hvbox hvbell
  have hge : ρ ≤ mdpOptimalGain M :=
    BanditAlgorithm.mdp_optimal_gain_ge_of_reverse_bellman_ineq hS M g ρ v (-mdpDiameter M) (mdpDiameter M) hvbox
      fun s ↦ le_of_eq (hveq s)
  exact ⟨ρ, v, g, hlimmem.2.1, hlimmem.2.2, hvspan, hvbell, hveq, le_antisymm hle hge⟩
