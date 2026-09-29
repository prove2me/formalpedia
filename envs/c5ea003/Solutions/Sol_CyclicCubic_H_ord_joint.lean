-- Prove2me | solution 1 for CyclicCubic.H_ord_joint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:12:18.597749+00:00
-- url     : https://prove2.me/submissions/453db160-0349-41e2-acba-c23cf7d5fe3a

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


private lemma logb_eighteen : Real.logb 2 18 = 1 + 2 * Real.logb 2 3 := by
  rw [show (18 : ℝ) = 2 * 3 ^ 2 by norm_num, Real.logb_mul (by norm_num) (by norm_num),
    Real.logb_pow]
  simp

private lemma nlp_inv (n : ℝ) : nlp (1 / n) = (1 / n) * Real.logb 2 n := by
  rw [nlp, one_div, Real.logb_inv]; ring


private lemma nlp_one_ninth : nlp (1 / 9) = 2 * Real.logb 2 3 / 9 := by
  rw [nlp_inv 9, logb_nine]; ring

private lemma nlp_one_eighteenth : nlp (1 / 18) = (1 + 2 * Real.logb 2 3) / 18 := by
  rw [nlp_inv 18, logb_eighteen]; ring





/-! ## Numerical bounds on `log₂ 3` -/



/-! ## The type map -/




/-! ## The single-prime channel `p mod 7 ⟶ type` -/

















/-! ## The semiprime channel `N = p·q mod 7 ⟶ unordered type pair` -/






instance (n : ZMod 7) : Decidable (clsB n) := by unfold clsB; infer_instance















/-! ## Which factor is which: exactly zero bits -/



lemma countOrd_eq : ∀ n b, countOrd n b =
    if clsA n ∧ b = (false, false) then 4
    else if (clsA n ∧ b = (true, true)) ∨ (clsB n ∧ b ≠ (true, true)) then 2 else 0 := by decide




lemma pOrd_eq (q : ZMod 7 × (Bool × Bool)) :
    pOrd q = if clsA q.1 ∧ q.2 = (false, false) then 1 / 9
      else if (clsA q.1 ∧ q.2 = (true, true)) ∨ (clsB q.1 ∧ q.2 ≠ (true, true)) then 1 / 18
      else 0 := by
  simp only [pOrd, countOrd_eq]
  split
  · norm_num
  · split <;> norm_num











open CyclicCubic in
theorem solution: H Finset.univ pOrd = 2 * Real.logb 2 3 + 7 / 9 := by
  have hfun : pOrd = fun q : ZMod 7 × (Bool × Bool) =>
      if clsA q.1 ∧ q.2 = (false, false) then (1 : ℝ) / 9
      else if (clsA q.1 ∧ q.2 = (true, true)) ∨ (clsB q.1 ∧ q.2 ≠ (true, true)) then 1 / 18
      else 0 := funext pOrd_eq
  rw [hfun, H_ite_three (fun q : ZMod 7 × (Bool × Bool) => clsA q.1 ∧ q.2 = (false, false))
      (fun q : ZMod 7 × (Bool × Bool) =>
        (clsA q.1 ∧ q.2 = (true, true)) ∨ (clsB q.1 ∧ q.2 ≠ (true, true))) (1 / 9) (1 / 18) 0,
    show (Finset.univ.filter (fun q : ZMod 7 × (Bool × Bool) =>
      clsA q.1 ∧ q.2 = (false, false))).card = 2 from by decide,
    show (Finset.univ.filter (fun q : ZMod 7 × (Bool × Bool) =>
      ¬(clsA q.1 ∧ q.2 = (false, false)) ∧
        ((clsA q.1 ∧ q.2 = (true, true)) ∨ (clsB q.1 ∧ q.2 ≠ (true, true))))).card = 14 from
      by decide,
    nlp_one_ninth, nlp_one_eighteenth]
  simp only [nlp, Real.logb_zero, mul_zero, neg_zero, add_zero]
  push_cast
  ring
