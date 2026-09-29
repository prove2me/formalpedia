-- Prove2me | solution 1 for A4ForkPinning.info_leak_strict
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:23:17.562421+00:00
-- url     : https://prove2.me/submissions/25986a0b-252d-48f4-a736-35886d4e45ea

-- Sol generated from Algebra/A4ForkPinning/Information.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Theorems.Thm_A4ForkPinning_hb_zero
import Theorems.Thm_A4ForkPinning_info_leak
import Theorems.Thm_A4ForkPinning_log_two_pos
/-
# Fork information: the pinned / flat / leaking trichotomy

Formal core of the *A4-FORK-PINNING* experiment (paper 75, experiment 410).

A **fork** attached to a number field is a binary observable `F` of the Frobenius
class of a prime `p`; a **dial** is a residue datum `y = p mod m`.  The
experiment measures the mutual information `I(y ; F)` and observes exactly three
regimes:

* **pinned**   — `F` is a function of `y`, and `I = H(F)` is maximal;
* **flat**     — `F` is independent of `y`, and `I = 0`;
* **leaking**  — `F` is a *thinning* of a pinned event, and `0 < I < H(F)`,
  with the exact closed form `I = H(pq) - p·H(q)`.

This file builds the (bit-valued) information calculus needed to state and prove
those three laws for an arbitrary finite dial:

* `A4ForkPinning.info_of_pinned`   — pinned forks realise `I = H(F)`;
* `A4ForkPinning.info_of_flat`     — flat forks realise `I = 0`;
* `A4ForkPinning.info_leak`        — the **exact leakage law** `I = H(pq) - p·H(q)`;
* `A4ForkPinning.info_leak_strict` — leakage is strictly between the two regimes;
* `A4ForkPinning.info_trichotomy`  — `0 ≤ I ≤ H(F)`, with `I = 0` iff the fork is
  flat and `I = H(F)` iff the fork is pinned (strict Jensen in both directions).

All entropies are measured in **bits** (`negMulLog` divided by `log 2`).
-/

open A4ForkPinning

open Real Finset Set

/-! ## Bit-valued entropy -/







lemma nml_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ nml x :=
  div_nonneg (Real.negMulLog_nonneg h0 h1) log_two_pos.le

lemma nml_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < nml x := by
  have h : 0 < Real.negMulLog x := by
    rw [Real.negMulLog]
    have := Real.log_neg h0 h1
    nlinarith
  exact div_pos h log_two_pos






lemma hb_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < hb x :=
  add_pos_of_pos_of_nonneg (nml_pos h0 h1) (nml_nonneg (by linarith) (by linarith))


/-! ## Concavity -/

lemma strictConcaveOn_nml : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) nml := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy hxy a b ha hb' hab
  have h := Real.strictConcaveOn_negMulLog.2 hx hy hxy ha hb' hab
  simp only [nml, smul_eq_mul] at *
  rw [show a * (Real.negMulLog x / Real.log 2) + b * (Real.negMulLog y / Real.log 2)
      = (a * Real.negMulLog x + b * Real.negMulLog y) / Real.log 2 by ring]
  exact (div_lt_div_iff_of_pos_right log_two_pos).2 h

lemma strictConcaveOn_hb : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) hb := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb' hab
  have h1 := strictConcaveOn_nml.2 (Set.mem_Ici.2 hx.1) (Set.mem_Ici.2 hy.1) hxy ha hb' hab
  have h2 := strictConcaveOn_nml.2 (x := 1 - x) (y := 1 - y)
      (Set.mem_Ici.2 (by linarith [hx.2])) (Set.mem_Ici.2 (by linarith [hy.2]))
      (by intro h; apply hxy; linarith) ha hb' hab
  simp only [smul_eq_mul] at *
  rw [show a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) by nlinarith [hab]] at h2
  simp only [hb]
  linarith

/-- **Strict entropy gain of a thinning.**  For `0 < p < 1` and `0 < q ≤ 1`,
`p·H(q) < H(pq)`: diluting a `q`-biased coin by an independent `p`-coin strictly
increases the entropy.  This is the engine of the leakage law. -/
lemma hb_thinning_lt {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    p * hb q < hb (p * q) := by
  have h := strictConcaveOn_hb.2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show q ∈ Set.Icc (0 : ℝ) 1 from ⟨hq0.le, hq1⟩) (ne_of_lt hq0)
    (show (0 : ℝ) < 1 - p by linarith) hp0 (by ring)
  simp only [smul_eq_mul, hb_zero, mul_zero, zero_add] at h
  linarith

/-! ## The dial → fork channel -/

variable {Y : Type*} [Fintype Y]





  -- `simp only` above already closes the goal

/-! ### Pinned forks -/


/-! ### Flat forks -/


/-! ### Leaking forks -/



/-! ### The trichotomy -/





open A4ForkPinning in
theorem solution(w g : Y → ℝ) (q : ℝ) (hg : ∀ y, g y = 0 ∨ g y = 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < avg w g) (hp1 : avg w g < 1) :
    0 < info w (fun y => q * g y) ∧
      info w (fun y => q * g y) < hb (avg w (fun y => q * g y)) := by
  have hav : avg w (fun y => q * g y) = q * avg w g := by
    simp only [avg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [info_leak w g q hg, hav]
  refine ⟨?_, ?_⟩
  · have := hb_thinning_lt hp0 hp1 hq0 hq1.le
    rw [mul_comm q (avg w g)]
    linarith
  · have : 0 < avg w g * hb q := mul_pos hp0 (hb_pos hq0 hq1)
    linarith
