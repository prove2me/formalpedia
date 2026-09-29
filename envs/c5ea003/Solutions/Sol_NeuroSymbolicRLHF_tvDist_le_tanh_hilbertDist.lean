-- Prove2me | solution 1 for NeuroSymbolicRLHF.tvDist_le_tanh_hilbertDist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:08:01.478335+00:00
-- url     : https://prove2.me/submissions/12ac62e8-5c5a-44b8-9fb1-8b555585bd31

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {p q : ι → ℝ} (hp : IsPosProb p)
    (hq : IsPosProb q) :
    tvDist p q
      ≤ (Real.exp (hilbertDist p q / 2) - 1) / (Real.exp (hilbertDist p q / 2) + 1) := by
  -- algebraic core: an odds-ratio bound `x(1-y) ≤ s² y(1-x)` caps `x - y` by `(s-1)/(s+1)`
  have key : ∀ x y s : ℝ, 0 ≤ y → y ≤ x → x ≤ 1 → 1 ≤ s →
      x * (1 - y) ≤ s ^ 2 * (y * (1 - x)) → (x - y) * (s + 1) ≤ s - 1 := by
    intro x y s hy hyx hx1 hs H
    have hf : x * (1 - y) * (1 - x + y) ^ 2 - y * (1 - x) * (1 + x - y) ^ 2
        = (x - y) * (x + y - 1) ^ 2 := by ring
    rcases (mul_nonneg hy (sub_nonneg.2 hx1)).eq_or_lt with h0 | hpos
    · have hle : x * (1 - y) ≤ 0 := by rw [← h0, mul_zero] at H; exact H
      have hx0 : 0 ≤ x := hy.trans hyx
      have heq : x * (1 - y) = 0 := le_antisymm hle (mul_nonneg hx0 (by linarith))
      have hxy : x = y := by
        rcases mul_eq_zero.mp heq with h | h
        · linarith
        · linarith
      rw [hxy, sub_self, zero_mul]
      linarith
    · by_contra hlt
      replace hlt := not_le.mp hlt
      have hsab : s * (1 - x + y) < 1 + x - y := by linarith
      have hsq : 0 < (1 + x - y) ^ 2 - (s * (1 - x + y)) ^ 2 := by
        have e : (1 + x - y) ^ 2 - (s * (1 - x + y)) ^ 2
            = (1 + x - y - s * (1 - x + y)) * (1 + x - y + s * (1 - x + y)) := by ring
        rw [e]
        exact mul_pos (by linarith) (by nlinarith)
      have h1 := mul_le_mul_of_nonneg_right H (sq_nonneg (1 - x + y))
      have h2 : 0 ≤ (x - y) * (x + y - 1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have h3 := mul_pos hpos hsq
      nlinarith [h1, h2, hf, h3]
  have hpos := hp.pos
  have hqpos := hq.pos
  obtain ⟨f, hf⟩ : ∃ f : ι → ℝ, f = fun i => Real.log (p i / q i) := ⟨_, rfl⟩
  have hH : hilbertDist p q = univ.sup' univ_nonempty f - univ.inf' univ_nonempty f := by
    rw [hf]
    rfl
  have hfi : ∀ i, p i / q i = Real.exp (f i) := fun i => by
    rw [hf, Real.exp_log (div_pos (hpos i) (hqpos i))]
  obtain ⟨M, hM⟩ : ∃ M, M = Real.exp (univ.sup' univ_nonempty f) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = Real.exp (univ.inf' univ_nonempty f) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Real.exp (hilbertDist p q / 2) := ⟨_, rfl⟩
  rw [← hs]
  have hm0 : 0 < m := hm ▸ Real.exp_pos _
  have hub : ∀ i, p i ≤ M * q i := by
    intro i
    have h3 : p i / q i ≤ M := by
      rw [hfi, hM]
      exact Real.exp_le_exp.2 (le_sup' f (mem_univ i))
    rwa [div_le_iff₀ (hqpos i)] at h3
  have hlb : ∀ i, m * q i ≤ p i := by
    intro i
    have h3 : m ≤ p i / q i := by
      rw [hfi, hm]
      exact Real.exp_le_exp.2 (inf'_le f (mem_univ i))
    rwa [le_div_iff₀ (hqpos i)] at h3
  have hs2 : s ^ 2 * m = M := by
    rw [hs, hm, hM, hH, sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hs1 : 1 ≤ s := by
    obtain ⟨i0⟩ := ‹Nonempty ι›
    rw [hs, hH]
    exact Real.one_le_exp (by linarith [inf'_le f (mem_univ i0), le_sup' f (mem_univ i0)])
  -- split along `A = {q ≤ p}`
  have hsp := sum_filter_add_sum_filter_not univ (fun i => q i ≤ p i) p
  have hsq := sum_filter_add_sum_filter_not univ (fun i => q i ≤ p i) q
  have hsa := sum_filter_add_sum_filter_not univ (fun i => q i ≤ p i) (fun i => |p i - q i|)
  rw [hp.sum_one] at hsp
  rw [hq.sum_one] at hsq
  have hA : ∑ i ∈ univ.filter (fun i => q i ≤ p i), |p i - q i|
      = ∑ i ∈ univ.filter (fun i => q i ≤ p i), p i
        - ∑ i ∈ univ.filter (fun i => q i ≤ p i), q i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun i hi => abs_of_nonneg (sub_nonneg.2 (mem_filter.1 hi).2))
  have hAc : ∑ i ∈ univ.filter (fun i => ¬ q i ≤ p i), |p i - q i|
      = ∑ i ∈ univ.filter (fun i => ¬ q i ≤ p i), q i
        - ∑ i ∈ univ.filter (fun i => ¬ q i ≤ p i), p i := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl (fun i hi => ?_)
    rw [abs_of_neg (sub_neg.2 (not_le.1 (mem_filter.1 hi).2))]
    ring
  have hxM : ∑ i ∈ univ.filter (fun i => q i ≤ p i), p i
      ≤ M * ∑ i ∈ univ.filter (fun i => q i ≤ p i), q i := by
    rw [mul_sum]
    exact sum_le_sum (fun i _ => hub i)
  have hxm : m * ∑ i ∈ univ.filter (fun i => ¬ q i ≤ p i), q i
      ≤ ∑ i ∈ univ.filter (fun i => ¬ q i ≤ p i), p i := by
    rw [mul_sum]
    exact sum_le_sum (fun i _ => hlb i)
  have hyx : ∑ i ∈ univ.filter (fun i => q i ≤ p i), q i
      ≤ ∑ i ∈ univ.filter (fun i => q i ≤ p i), p i :=
    sum_le_sum (fun i hi => (mem_filter.1 hi).2)
  have hy0 : 0 ≤ ∑ i ∈ univ.filter (fun i => q i ≤ p i), q i :=
    sum_nonneg (fun i _ => (hqpos i).le)
  have hpc0 : 0 ≤ ∑ i ∈ univ.filter (fun i => ¬ q i ≤ p i), p i :=
    sum_nonneg (fun i _ => (hpos i).le)
  obtain ⟨x, hx⟩ : ∃ x, x = ∑ i ∈ univ.filter (fun i => q i ≤ p i), p i := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = ∑ i ∈ univ.filter (fun i => q i ≤ p i), q i := ⟨_, rfl⟩
  rw [← hx] at hsp hA hxM hyx
  rw [← hy] at hsq hA hxM hyx hy0
  have hcq : ∑ i ∈ univ.filter (fun i => ¬ q i ≤ p i), q i = 1 - y := by linarith
  rw [hcq] at hxm
  have h1x : m * (1 - y) ≤ 1 - x := by linarith
  have hprod := mul_le_mul hxM h1x (mul_nonneg hm0.le (by linarith)) (by nlinarith)
  rw [← hs2] at hprod
  have H : x * (1 - y) ≤ s ^ 2 * (y * (1 - x)) := by
    have : m * (x * (1 - y)) ≤ m * (s ^ 2 * (y * (1 - x))) := by linarith
    exact le_of_mul_le_mul_left this hm0
  have hk := key x y s hy0 hyx (by linarith) hs1 H
  have hTV : tvDist p q = x - y := by
    unfold tvDist
    linarith
  rw [hTV, le_div_iff₀ (by linarith)]
  exact hk
