-- Prove2me | solution 1 for CyclicCubic.H_ord_pair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:12:19.111964+00:00
-- url     : https://prove2.me/submissions/d6b985fd-ac33-4a8b-874d-0f6fe3fac268

-- Sol generated from Applications/CyclicCubicTypeChannel/Entropy.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Entropy
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_LabelEntropyDeficit
/-
# The cyclic-cubic type channel: full pinning, and its failure for semiprimes

## Context (FACT round-32 #3, "THE-CYCLIC-CUBIC-IS-FULLY-PINNED", paper 122)

`Applications.CyclicCubicTypeChannel.Splitting` proves the arithmetic law: an
unramified prime `p` has residue degree `1` in `K = ℚ(ζ₇ + ζ₇⁻¹)` iff
`p ≡ ±1 (mod 7)`, and residue degree `3` otherwise — **two types only**.

This file turns that law into an information channel and computes its capacity
exactly, in bits, using the Shannon-entropy functional of
`Applications.LabelEntropyDeficit`.  Modelling `p mod 7` as uniform on the six
invertible residues (Chebotarev/Dirichlet equidistribution), we prove:

* `CyclicCubic.H_typeMarginal` — the type entropy is exactly
  `H(T) = log₂ 3 − 2/3 = 0.918296…` bits (experiment: `0.9179`);
* `CyclicCubic.mutualInfo_residue_type` — `I(p mod 7 ; T) = log₂ 3 − 2/3`, i.e.
  `I = H(T)` **exactly**: the type is fully pinned by the residue
  (`CyclicCubic.full_pinning`), and the channel leaks nothing more
  (`CyclicCubic.pinning_saturates`, `I ≤ H(T)` with equality);
* `CyclicCubic.mutualInfo_semiprime` — for a *semiprime* `N = p·q` the residue
  `N mod 7` retains only `log₂ 3 − 10/9 = 0.473852…` bits about the unordered
  type pair (experiment: `0.4747`): pinning is destroyed by multiplication;
* `CyclicCubic.which_factor_information_zero` — the *ordered* type pair carries
  exactly the same information as the unordered one, so the residue reveals
  **0.0000** bits about *which* factor has which type; the underlying exact
  symmetry is `CyclicCubic.countOrd_swap`.

All entropies are computed in closed form; numerical bounds
(`CyclicCubic.H_typeMarginal_bounds`, `CyclicCubic.mutualInfo_semiprime_bounds`)
are derived from kernel-checked integer inequalities `2^1584 < 3^1000 < 2^1585`.
-/

open Finset LabelEntropy

open CyclicCubic

/-! ## Entropy of a finitely-valued distribution given in case form -/


variable {ι : Type*} [Fintype ι]


/-- Entropy of a distribution with three constant values. -/
lemma H_ite_three (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q] (a b c : ℝ) :
    H Finset.univ (fun i => if P i then a else if Q i then b else c)
      = (Finset.univ.filter P).card * nlp a
        + (Finset.univ.filter (fun i => ¬ P i ∧ Q i)).card * nlp b
        + (Finset.univ.filter (fun i => ¬ P i ∧ ¬ Q i)).card * nlp c := by
  unfold H
  simp only [apply_ite nlp]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Finset.filter_filter, Finset.filter_filter,
    add_assoc]



/-! ## Mutual information of a joint distribution -/


/-! ## Logarithm values -/

private lemma logb_nine : Real.logb 2 9 = 2 * Real.logb 2 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.logb_pow]; push_cast; ring



private lemma nlp_inv (n : ℝ) : nlp (1 / n) = (1 / n) * Real.logb 2 n := by
  rw [nlp, one_div, Real.logb_inv]; ring


private lemma nlp_one_ninth : nlp (1 / 9) = 2 * Real.logb 2 3 / 9 := by
  rw [nlp_inv 9, logb_nine]; ring




private lemma nlp_four_ninths : nlp (4 / 9) = (2 * Real.logb 2 3 - 2) * 4 / 9 := by
  have h : (4 : ℝ) / 9 = 1 / (9 / 4) := by norm_num
  rw [h, nlp_inv (9 / 4), Real.logb_div (by norm_num) (by norm_num), logb_nine,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow]
  simp
  ring

private lemma nlp_two_ninths : nlp (2 / 9) = (2 * Real.logb 2 3 - 1) * 2 / 9 := by
  have h : (2 : ℝ) / 9 = 1 / (9 / 2) := by norm_num
  rw [h, nlp_inv (9 / 2), Real.logb_div (by norm_num) (by norm_num), logb_nine]
  simp
  ring

/-! ## Numerical bounds on `log₂ 3` -/



/-! ## The type map -/




/-! ## The single-prime channel `p mod 7 ⟶ type` -/

















/-! ## The semiprime channel `N = p·q mod 7 ⟶ unordered type pair` -/






instance (n : ZMod 7) : Decidable (clsB n) := by unfold clsB; infer_instance















/-! ## Which factor is which: exactly zero bits -/





lemma countOrd_sum_n : ∀ b : Bool × Bool, ∑ n : ZMod 7, countOrd n b =
    if b = (true, true) then 4 else if b = (false, false) then 16 else 8 := by decide





lemma pOrd_marginal_pair (b : Bool × Bool) :
    (∑ n : ZMod 7, pOrd (n, b))
      = if b = (true, true) then 1 / 9 else if b = (false, false) then 4 / 9 else 2 / 9 := by
  have h : (∑ n : ZMod 7, pOrd (n, b)) = ((∑ n : ZMod 7, countOrd n b : ℕ) : ℝ) / 36 := by
    simp only [pOrd, ← Finset.sum_div]
    push_cast
    rfl
  rw [h, countOrd_sum_n b]
  split
  · norm_num
  · split <;> norm_num








open CyclicCubic in
theorem solution:
    H Finset.univ (fun b : Bool × Bool => ∑ n : ZMod 7, pOrd (n, b))
      = 2 * Real.logb 2 3 - 4 / 3 := by
  have hfun : (fun b : Bool × Bool => ∑ n : ZMod 7, pOrd (n, b))
      = fun b : Bool × Bool => if b = (true, true) then (1 : ℝ) / 9
        else if b = (false, false) then 4 / 9 else 2 / 9 := funext pOrd_marginal_pair
  rw [hfun, H_ite_three (fun b : Bool × Bool => b = (true, true))
      (fun b : Bool × Bool => b = (false, false)) (1 / 9) (4 / 9) (2 / 9),
    show (Finset.univ.filter (fun b : Bool × Bool => b = (true, true))).card = 1 from by decide,
    show (Finset.univ.filter (fun b : Bool × Bool =>
      ¬ b = (true, true) ∧ b = (false, false))).card = 1 from by decide,
    show (Finset.univ.filter (fun b : Bool × Bool =>
      ¬ b = (true, true) ∧ ¬ b = (false, false))).card = 2 from by decide,
    nlp_one_ninth, nlp_four_ninths, nlp_two_ninths]
  push_cast
  ring
