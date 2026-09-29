-- Prove2me | solution 1 for Bishop.no_continuous_root_selector
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:39:44.732219+00:00
-- url     : https://prove2.me/submissions/5846353a-8073-40c0-86ad-f78e51c5b6ea

-- Sol generated from Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BrouwerianCounterexamples
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
/-
# A Brouwerian counterexample: the exact IVT has no continuous solution operator

This file makes precise the sense in which the *exact* intermediate value theorem
fails constructively, while the approximate one (proved in
`Logic/ConstructiveAnalysis/ConstructiveIVT.lean`) holds.

We use Bishop's standard family of "shelf" functions

  `shelf t x = min (x - 1) (max t (x - 2))`,   `t ∈ [-1,1]`, `x ∈ [0,3]`.

Each `shelf t` is `1`-Lipschitz (so it has the explicit modulus of uniform
continuity `ω = id`), and satisfies `shelf t 0 ≤ 0 ≤ shelf t 3`, so the approximate
IVT applies to the whole family uniformly (`shelf_approx_root`).  Nevertheless:

* `shelf_root_of_mem_Ioo` : if `1 < x < 2` and `shelf t x = 0` then `t = 0`;
* `no_continuous_root_selector` : there is **no continuous** map `t ↦ r t` on
  `[-1,1]` with `shelf t (r t) = 0`.

Since every constructively (in particular, computably) defined map `ℝ → ℝ` is
continuous, this shows that no constructive proof of the exact IVT can exist: the
root cannot be obtained continuously — let alone computably — from the data.
The hypothesis that rescues the exact IVT in `constructive_ivt` is a positive lower
slope bound; `shelf_zero_slope_bound_nonpos` shows that this is precisely what the
family violates at `t = 0`, where `shelf 0` is constant on `[1,2]`.
-/


open Bishop

open Set







/-- A root strictly between `1` and `2` can only occur at the parameter `t = 0`. -/
theorem shelf_root_of_mem_Ioo {t x : ℝ} (h1 : 1 < x) (h2 : x < 2) (h : shelf t x = 0) :
    t = 0 := by
  simp only [shelf] at h
  rcases min_cases (x - 1) (max t (x - 2)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h
  · linarith
  · rcases max_cases t (x - 2) with ⟨he2, _⟩ | ⟨he2, _⟩ <;> rw [he2] at h <;> linarith

/-- At the parameter `t = 1` the unique root is `x = 1`. -/
theorem shelf_one_root {x : ℝ} (h : shelf 1 x = 0) : x = 1 := by
  simp only [shelf] at h
  rcases min_cases (x - 1) (max 1 (x - 2)) with ⟨he, hle⟩ | ⟨he, hle⟩ <;> rw [he] at h
  · linarith
  · rcases max_cases (1 : ℝ) (x - 2) with ⟨he2, _⟩ | ⟨he2, _⟩ <;> rw [he2] at h <;> linarith

/-- At the parameter `t = -1` the unique root is `x = 2`. -/
theorem shelf_neg_one_root {x : ℝ} (h : shelf (-1) x = 0) : x = 2 := by
  simp only [shelf] at h
  rcases min_cases (x - 1) (max (-1 : ℝ) (x - 2)) with ⟨he, hle⟩ | ⟨he, hle⟩ <;> rw [he] at h
  · rcases max_cases (-1 : ℝ) (x - 2) with ⟨he2, hlt⟩ | ⟨he2, hlt⟩ <;>
      rw [he2] at hle <;> linarith
  · rcases max_cases (-1 : ℝ) (x - 2) with ⟨he2, _⟩ | ⟨he2, _⟩ <;> rw [he2] at h <;> linarith





open Bishop in
theorem solution:
    ¬ ∃ r : ℝ → ℝ, ContinuousOn r (Icc (-1 : ℝ) 1) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, shelf t (r t) = 0 := by
  rintro ⟨r, hcont, hroot⟩
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hr1 : r 1 = 1 := shelf_one_root (hroot 1 hp1)
  have hrm1 : r (-1) = 2 := shelf_neg_one_root (hroot (-1) hm1)
  have hsub : Icc (r 1) (r (-1)) ⊆ r '' Icc (-1 : ℝ) 1 :=
    intermediate_value_Icc' (by norm_num) hcont
  rw [hr1, hrm1] at hsub
  obtain ⟨t₀, ht₀, hv₀⟩ := hsub (show (3 / 2 : ℝ) ∈ Icc (1 : ℝ) 2 by norm_num)
  obtain ⟨t₁, ht₁, hv₁⟩ := hsub (show (7 / 4 : ℝ) ∈ Icc (1 : ℝ) 2 by norm_num)
  have h0 : t₀ = 0 := by
    refine shelf_root_of_mem_Ioo (x := r t₀) ?_ ?_ (hroot t₀ ht₀)
    · rw [hv₀]; norm_num
    · rw [hv₀]; norm_num
  have h1 : t₁ = 0 := by
    refine shelf_root_of_mem_Ioo (x := r t₁) ?_ ?_ (hroot t₁ ht₁)
    · rw [hv₁]; norm_num
    · rw [hv₁]; norm_num
  rw [h0] at hv₀
  rw [h1] at hv₁
  rw [hv₀] at hv₁
  norm_num at hv₁
