-- Prove2me | solution 1 for lean_workbook_plus_58081
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:08:42.949837+00:00
-- url     : https://prove2.me/submissions/00cb8ff9-32e4-469b-805d-599dc9a8b7b9

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter

theorem cyclic_jensen_midpoint (f : ℝ → ℝ) (hf : Continuous f)
    (hfe : ∀ x y z : ℝ,
      f ((x + 2 * y) / 3) + f ((y + 2 * z) / 3) + f ((z + 2 * x) / 3) =
        f x + f y + f z) (x y : ℝ) :
    2 * f ((x + y) / 2) = f x + f y := by
  have hcontract (c t : ℝ) :
      f (c + t / 3) + f (c - t / 3) = f (c + t) + f (c - t) := by
    have h := hfe (c + t) (c - t) (c + t)
    have h1 : (c + t + 2 * (c - t)) / 3 = c - t / 3 := by ring
    have h2 : (c - t + 2 * (c + t)) / 3 = c + t / 3 := by ring
    have h3 : (c + t + 2 * (c + t)) / 3 = c + t := by ring
    rw [h1, h2, h3] at h
    linarith
  let c : ℝ := (x + y) / 2
  let t : ℝ := (x - y) / 2
  have hsum (n : ℕ) :
      f (c + t * (1 / 3 : ℝ) ^ n) + f (c - t * (1 / 3 : ℝ) ^ n) = f x + f y := by
    induction n with
    | zero =>
        have h1 : c + t * (1 / 3 : ℝ) ^ 0 = x := by dsimp [c, t]; ring
        have h2 : c - t * (1 / 3 : ℝ) ^ 0 = y := by dsimp [c, t]; ring
        rw [h1, h2]
    | succ n ih =>
        have h1 : t * (1 / 3 : ℝ) ^ (n + 1) = (t * (1 / 3 : ℝ) ^ n) / 3 := by
          rw [pow_succ]
          ring
        rw [h1, hcontract, ih]
  have hp : Tendsto (fun n : ℕ => (1 / 3 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hplus : Tendsto (fun n : ℕ => c + t * (1 / 3 : ℝ) ^ n) atTop (nhds c) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hp.const_mul t)
  have hminus : Tendsto (fun n : ℕ => c - t * (1 / 3 : ℝ) ^ n) atTop (nhds c) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hp.const_mul t)
  have hlim := (hf.continuousAt.tendsto.comp hplus).add
    (hf.continuousAt.tendsto.comp hminus)
  have heq : (fun n : ℕ =>
      f (c + t * (1 / 3 : ℝ) ^ n) + f (c - t * (1 / 3 : ℝ) ^ n)) =
      (fun _ : ℕ => f x + f y) := funext hsum
  change Tendsto (fun n : ℕ =>
    f (c + t * (1 / 3 : ℝ) ^ n) + f (c - t * (1 / 3 : ℝ) ^ n))
    atTop (nhds (f c + f c)) at hlim
  rw [heq] at hlim
  have hc : f c + f c = f x + f y := tendsto_nhds_unique hlim tendsto_const_nhds
  change 2 * f c = f x + f y
  linarith

theorem continuous_cyclic_jensen_classification (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ x y z : ℝ,
      f ((x + 2 * y) / 3) + f ((y + 2 * z) / 3) + f ((z + 2 * x) / 3) =
        f x + f y + f z) ↔
      ∀ x : ℝ, f x = (f 1 - f 0) * x + f 0 := by
  constructor
  · intro hfe
    have hadd (u v : ℝ) : f (u + v) - f 0 = (f u - f 0) + (f v - f 0) := by
      have h1 := cyclic_jensen_midpoint f hf hfe u v
      have h2 := cyclic_jensen_midpoint f hf hfe (u + v) 0
      rw [add_zero] at h2
      linarith
    let g : ℝ →+ ℝ :=
      { toFun := fun x => f x - f 0
        map_zero' := sub_self _
        map_add' := hadd }
    have hg : Continuous g := hf.sub continuous_const
    intro x
    have hlin := map_real_smul g hg x (1 : ℝ)
    change f (x * 1) - f 0 = x * (f 1 - f 0) at hlin
    rw [mul_one] at hlin
    nlinarith
  · intro h x y z
    rw [h ((x + 2 * y) / 3), h ((y + 2 * z) / 3), h ((z + 2 * x) / 3),
      h x, h y, h z]
    ring

theorem solution : ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x y z : ℝ,
    f ((x + 2 * y) / 3) + f ((y + 2 * z) / 3) + f ((z + 2 * x) / 3) =
      f x + f y + f z := by
  refine ⟨id, continuous_id, ?_⟩
  apply (continuous_cyclic_jensen_classification id continuous_id).mpr
  intro x
  simp

#print axioms cyclic_jensen_midpoint
#print axioms continuous_cyclic_jensen_classification
#print axioms solution
