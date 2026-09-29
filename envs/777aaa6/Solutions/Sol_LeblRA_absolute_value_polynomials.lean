-- Prove2me | solution 1 for LeblRA.absolute_value_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:13:51.594709+00:00
-- url     : https://prove2.me/submissions/363b4469-ea9a-4e4b-b32c-dd100d4ddc6c

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA

private theorem real_polynomial_sequence (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    ∃ p : ℕ → ℝ[X], Tendsto (fun n => (p n).toContinuousMapOn (Set.Icc a b)) atTop (𝓝 f) := by
  have h : f ∈ closure (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) :=
    continuousMap_mem_polynomialFunctions_closure a b f
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp h
  have hpoly : ∀ n, ∃ p : ℝ[X], p.toContinuousMapOn (Set.Icc a b) = q n := by
    intro n
    have hn := hq n
    rw [polynomialFunctions_coe] at hn
    exact hn
  choose p hp using hpoly
  exact ⟨p, by simpa only [hp] using hlim⟩

theorem _root_.solution (a : ℝ) (ha : 0 ≤ a) :
    ∃ p : ℕ → ℝ[X], (∀ n, (p n).eval 0 = 0) ∧
      TendstoUniformly (fun n (x : Set.Icc (-a) a) => (p n).eval (x : ℝ))
        (fun x : Set.Icc (-a) a => |(x : ℝ)|) atTop := by
  let f : C(Set.Icc (-a) a, ℝ) := ⟨fun x => |(x : ℝ)|, continuous_abs.comp continuous_subtype_val⟩
  obtain ⟨p, hp⟩ := real_polynomial_sequence (-a) a f
  let z : Set.Icc (-a) a := ⟨0, ⟨neg_nonpos.mpr ha, ha⟩⟩
  have hz : Tendsto (fun n => (p n).eval 0) atTop (𝓝 (0 : ℝ)) := by
    simpa [f, z] using (continuous_eval_const z).tendsto f |>.comp hp
  have hc : Tendsto (fun n => ContinuousMap.const (Set.Icc (-a) a) ((p n).eval 0)) atTop (𝓝 (0 : C(Set.Icc (-a) a, ℝ))) := by
    have hh : Continuous (ContinuousMap.const (Set.Icc (-a) a) : ℝ → C(Set.Icc (-a) a, ℝ)) := ContinuousMap.continuous_const'
    simpa using hh.tendsto (0 : ℝ) |>.comp hz
  refine ⟨fun n => p n - Polynomial.C ((p n).eval 0), by simp, ?_⟩
  convert ContinuousMap.tendsto_iff_tendstoUniformly.mp (hp.sub hc) using 1
  · ext n x
    simp
  · ext x
    simp [f]

end LeblRA
