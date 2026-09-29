-- Prove2me | solution 1 for A4ForkPinning.info_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:23:17.031353+00:00
-- url     : https://prove2.me/submissions/c15a4ae8-b491-4c28-9f1b-a54a970929e6

-- Sol generated from Algebra/A4ForkPinning/Information.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Theorems.Thm_A4ForkPinning_hb_zero
import Theorems.Thm_A4ForkPinning_info_of_pinned
import Theorems.Thm_A4ForkPinning_log_two_pos
import Theorems.Thm_A4ForkPinning_nml_zero
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






@[simp] lemma nml_one : nml 1 = 0 := by simp [nml]

lemma nml_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ nml x :=
  div_nonneg (Real.negMulLog_nonneg h0 h1) log_two_pos.le

lemma nml_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < nml x := by
  have h : 0 < Real.negMulLog x := by
    rw [Real.negMulLog]
    have := Real.log_neg h0 h1
    nlinarith
  exact div_pos h log_two_pos


@[simp] lemma hb_one : hb 1 = 0 := by simp [hb]



lemma hb_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ hb x :=
  add_nonneg (nml_nonneg h0 h1) (nml_nonneg (by linarith) (by linarith))

lemma hb_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < hb x :=
  add_pos_of_pos_of_nonneg (nml_pos h0 h1) (nml_nonneg (by linarith) (by linarith))

/-- On `[0,1]` the binary entropy vanishes exactly at the two deterministic points. -/
lemma hb_eq_zero_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : hb x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact absurd h (ne_of_gt (hb_pos (lt_of_le_of_ne h0 (Ne.symm hc.1))
      (lt_of_le_of_ne h1 hc.2)))
  · rintro (rfl | rfl) <;> simp

/-! ## Concavity -/




/-! ## The dial → fork channel -/

variable {Y : Type*} [Fintype Y]





  -- `simp only` above already closes the goal

/-! ### Pinned forks -/


/-! ### Flat forks -/


/-! ### Leaking forks -/



/-! ### The trichotomy -/





open A4ForkPinning in
theorem solution(w f : Y → ℝ) (hw : ∀ y, 0 < w y) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) : info w f = hb (avg w f) ↔ ∀ y, f y = 0 ∨ f y = 1 := by
  constructor
  · intro h y
    have hzero : condEntropy w f = 0 := by simp only [info] at h; linarith
    have hy := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hw y).le (hb_nonneg (hf0 y) (hf1 y)))).1 hzero y (Finset.mem_univ y)
    have hb0 : hb (f y) = 0 := by
      rcases mul_eq_zero.1 hy with h' | h'
      · exact absurd h' (ne_of_gt (hw y))
      · exact h'
    exact (hb_eq_zero_iff (hf0 y) (hf1 y)).1 hb0
  · exact fun h => info_of_pinned w f h
