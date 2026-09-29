-- Prove2me | solution 1 for LeblRA.polynomial_approximation
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:13:46.054119+00:00
-- url     : https://prove2.me/submissions/e645bd58-f783-4f6f-bee7-4c41c69b78c0

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

theorem _root_.solution (a b : ℝ) :
    (∀ f : C(Set.Icc a b, ℂ), ∃ p : ℕ → ℂ[X],
      TendstoUniformly (fun n (x : Set.Icc a b) => (p n).eval ((x : ℝ) : ℂ)) f atTop) ∧
    (∀ f : C(Set.Icc a b, ℝ), ∃ p : ℕ → ℝ[X],
      TendstoUniformly (fun n (x : Set.Icc a b) => (p n).eval (x : ℝ)) f atTop) := by
  have hcast (p : ℝ[X]) (x : ℝ) : (p.map Complex.ofRealHom).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply Complex.ofRealHom x
  constructor
  · intro f
    let R : C(Set.Icc a b, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
    let S : C(Set.Icc a b, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
    obtain ⟨p, hp⟩ := real_polynomial_sequence a b R
    obtain ⟨q, hq⟩ := real_polynomial_sequence a b S
    let J : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℂ) :=
      Complex.ofRealCLM.compLeftContinuous ℝ (Set.Icc a b)
    have hp' := (J.continuous.tendsto R).comp hp
    have hq' := (J.continuous.tendsto S).comp hq
    have hlim := hp'.add (hq'.const_smul Complex.I)
    refine ⟨fun n => (p n).map Complex.ofRealHom + Polynomial.C Complex.I * (q n).map Complex.ofRealHom, ?_⟩
    convert ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim using 1
    · ext n x
      simp [J, hcast]
    · ext x
      change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
      simpa [mul_comm] using (Complex.re_add_im (f x)).symm
  · intro f
    obtain ⟨p, hp⟩ := real_polynomial_sequence a b f
    exact ⟨p, ContinuousMap.tendsto_iff_tendstoUniformly.mp hp⟩

end LeblRA
