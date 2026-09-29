-- Prove2me | solution 1 for A4ForkPinning.info_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:26:04.605795+00:00
-- url     : https://prove2.me/submissions/484d9e20-96f9-4e50-bd1d-e886707f97ff

-- Sol generated from Algebra/A4ForkPinning/Information.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Theorems.Thm_A4ForkPinning_info_eq_top_iff
import Theorems.Thm_A4ForkPinning_info_of_flat
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






lemma hb_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ hb x :=
  add_nonneg (nml_nonneg h0 h1) (nml_nonneg (by linarith) (by linarith))



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


/-! ## The dial → fork channel -/

variable {Y : Type*} [Fintype Y]





  -- `simp only` above already closes the goal

/-! ### Pinned forks -/


/-! ### Flat forks -/


/-! ### Leaking forks -/



/-! ### The trichotomy -/

/-- Mutual information is bounded above by the entropy of the fork. -/
theorem info_le (w f : Y → ℝ) (hw : ∀ y, 0 ≤ w y) (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1) :
    info w f ≤ hb (avg w f) := by
  have h : 0 ≤ condEntropy w f :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hw y) (hb_nonneg (hf0 y) (hf1 y))
  simp only [info]
  linarith




open A4ForkPinning in
theorem solution(w f : Y → ℝ) [Nonempty Y] (hw : ∀ y, 0 < w y) (hsum : ∑ y, w y = 1)
    (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1) :
    0 ≤ info w f ∧ info w f ≤ hb (avg w f) ∧
      (info w f = 0 ↔ ∀ y y', f y = f y') ∧
      (info w f = hb (avg w f) ↔ ∀ y, f y = 0 ∨ f y = 1) := by
  have hmem : ∀ y ∈ (Finset.univ : Finset Y), f y ∈ Set.Icc (0 : ℝ) 1 :=
    fun y _ => ⟨hf0 y, hf1 y⟩
  have hJ : condEntropy w f ≤ hb (avg w f) := by
    have h := strictConcaveOn_hb.concaveOn.le_map_sum (t := (Finset.univ : Finset Y))
      (w := w) (p := f) (fun y _ => (hw y).le) hsum hmem
    simpa only [smul_eq_mul, condEntropy, avg] using h
  refine ⟨by simp only [info]; linarith, info_le w f (fun y => (hw y).le) hf0 hf1, ?_,
    info_eq_top_iff w f hw hf0 hf1⟩
  constructor
  · intro h
    have heq : hb (∑ y, w y • f y) = ∑ y, w y • hb (f y) := by
      simp only [smul_eq_mul]
      simp only [info, condEntropy, avg] at h
      linarith
    have hall := (strictConcaveOn_hb.map_sum_eq_iff (t := (Finset.univ : Finset Y))
      (fun y _ => hw y) hsum hmem).1 heq
    intro y y'
    rw [hall y (Finset.mem_univ y), hall y' (Finset.mem_univ y')]
  · intro h
    obtain ⟨y₀⟩ := ‹Nonempty Y›
    exact info_of_flat w f (f y₀) hsum (fun y => h y y₀)
