-- Prove2me | solution 1 for lean_workbook_plus_674
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:51:40.782742+00:00
-- url     : https://prove2.me/submissions/77e9033f-fb37-4f3b-a19c-5bfe7862f4c3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Bases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter Topology

theorem reciprocal_odd_even_value (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) (n : ℕ) :
    u (2 * n) = 1 / ((2 * n : ℕ) : ℝ) := by
  simpa using h (2 * n)

theorem reciprocal_odd_odd_value (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) (n : ℕ) :
    u (2 * n + 1) = ((2 * n + 1 : ℕ) : ℝ) := by
  simpa using h (2 * n + 1)

theorem reciprocal_odd_even_tendsto (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) :
    Tendsto (fun n => u (2 * n)) atTop (𝓝 0) := by
  have hi : StrictMono (fun n : ℕ => 2 * n) := by intro n m hnm; change 2 * n < 2 * m; omega
  have ht : Tendsto (fun n : ℕ => ((2 * n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hi.tendsto_atTop
  simpa only [Function.comp_apply, reciprocal_odd_even_value u h, one_div] using
    tendsto_inv_atTop_zero.comp ht

theorem reciprocal_odd_odd_tendsto (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) :
    Tendsto (fun n => u (2 * n + 1)) atTop atTop := by
  have hi : StrictMono (fun n : ℕ => 2 * n + 1) := by intro n m hnm; change 2 * n + 1 < 2 * m + 1; omega
  have ht : Tendsto (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hi.tendsto_atTop
  simpa only [reciprocal_odd_odd_value u h] using ht

theorem reciprocal_odd_subsequential_limit (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (L : ℝ)
    (hL : Tendsto (u ∘ φ) atTop (𝓝 L)) : L = 0 := by
  have ht : Tendsto (fun n : ℕ => (φ n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have hu : ∀ᶠ n : ℕ in atTop, u (φ n) < L + 1 := hL.eventually (gt_mem_nhds (lt_add_one L))
  have hl : ∀ᶠ n : ℕ in atTop, L + 1 < (φ n : ℝ) := ht.eventually (eventually_gt_atTop _)
  have heven : ∀ᶠ n : ℕ in atTop, φ n % 2 = 0 := by
    filter_upwards [hu, hl] with n hn hn'
    by_contra he
    have hv : u (φ n) = (φ n : ℝ) := by simpa only [if_neg he] using h (φ n)
    linarith
  have hinv : Tendsto (fun n : ℕ => 1 / (φ n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, one_div] using tendsto_inv_atTop_zero.comp ht
  have hz : Tendsto (u ∘ φ) atTop (𝓝 0) := by
    apply hinv.congr'
    filter_upwards [heven] with n hn
    have hv : u (φ n) = 1 / (φ n : ℝ) := by simpa only [if_pos hn] using h (φ n)
    exact hv.symm
  exact tendsto_nhds_unique hL hz

theorem reciprocal_odd_zero_cluster (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) :
    MapClusterPt 0 atTop u := by
  have hi : StrictMono (fun n : ℕ => 2 * n) := by intro n m hnm; change 2 * n < 2 * m; omega
  exact MapClusterPt.of_comp hi.tendsto_atTop (reciprocal_odd_even_tendsto u h).mapClusterPt

theorem reciprocal_odd_cluster_iff (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) (L : ℝ) :
    MapClusterPt L atTop u ↔ L = 0 := by
  constructor
  · intro hL
    obtain ⟨φ, hφ, ht⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hL
    exact reciprocal_odd_subsequential_limit u h φ hφ L ht
  · rintro rfl
    exact reciprocal_odd_zero_cluster u h

theorem reciprocal_odd_subsequence_iff (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) (L : ℝ) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 L)) ↔ L = 0 := by
  constructor
  · rintro ⟨φ, hφ, ht⟩
    exact reciprocal_odd_subsequential_limit u h φ hφ L ht
  · rintro rfl
    exact ⟨fun n => 2 * n, by intro n m hnm; change 2 * n < 2 * m; omega,
      reciprocal_odd_even_tendsto u h⟩

theorem reciprocal_odd_no_finite_limit (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) (L : ℝ) :
    ¬ Tendsto u atTop (𝓝 L) := by
  intro hL
  have hi : StrictMono (fun n : ℕ => 2 * n + 1) := by intro n m hnm; change 2 * n + 1 < 2 * m + 1; omega
  exact not_tendsto_nhds_of_tendsto_atTop (reciprocal_odd_odd_tendsto u h) L
    (hL.comp hi.tendsto_atTop)

theorem solution (u : ℕ → ℝ)
    (h : ∀ n, if n % 2 = 0 then u n = 1 / n else u n = n) :
    0 ∈ closure (Set.range u) := by
  exact isClosed_closure.mem_of_mapClusterPt (reciprocal_odd_zero_cluster u h)
    (Eventually.of_forall (fun n => subset_closure (Set.mem_range_self n)))

#print axioms reciprocal_odd_even_value
#print axioms reciprocal_odd_odd_value
#print axioms reciprocal_odd_even_tendsto
#print axioms reciprocal_odd_odd_tendsto
#print axioms reciprocal_odd_subsequential_limit
#print axioms reciprocal_odd_zero_cluster
#print axioms reciprocal_odd_cluster_iff
#print axioms reciprocal_odd_subsequence_iff
#print axioms reciprocal_odd_no_finite_limit
#print axioms solution
