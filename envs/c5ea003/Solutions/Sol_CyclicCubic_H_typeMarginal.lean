-- Prove2me | solution 1 for CyclicCubic.H_typeMarginal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:15:13.097333+00:00
-- url     : https://prove2.me/submissions/3fc257f5-20e3-4740-ac52-c5d796812716

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

/-- Entropy of a distribution with two constant values on a decidable partition. -/
lemma H_ite_two (P : ι → Prop) [DecidablePred P] (a b : ℝ) :
    H Finset.univ (fun i => if P i then a else b)
      = (Finset.univ.filter P).card * nlp a
        + (Finset.univ.filter (fun i => ¬ P i)).card * nlp b := by
  unfold H
  simp only [apply_ite nlp]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]




/-! ## Mutual information of a joint distribution -/


/-! ## Logarithm values -/




private lemma nlp_inv (n : ℝ) : nlp (1 / n) = (1 / n) * Real.logb 2 n := by
  rw [nlp, one_div, Real.logb_inv]; ring




private lemma nlp_one_third : nlp (1 / 3) = Real.logb 2 3 / 3 := by
  rw [nlp_inv 3]; ring

private lemma nlp_two_thirds : nlp (2 / 3) = (2 * Real.logb 2 3 - 2) / 3 := by
  have h : (2 : ℝ) / 3 = 1 / (3 / 2) := by norm_num
  rw [h, nlp_inv (3 / 2),
    show (3 : ℝ) / 2 = 3 / 2 from rfl, Real.logb_div (by norm_num) (by norm_num)]
  simp
  ring



/-! ## Numerical bounds on `log₂ 3` -/



/-! ## The type map -/




/-! ## The single-prime channel `p mod 7 ⟶ type` -/





lemma countRT_sum_res : ∀ b : Bool, ∑ n : ZMod 7, countRT n b = if b then 2 else 4 := by decide





/-- Type marginal: `1/3` split, `2/3` inert. -/
lemma pRT_marginal_type (b : Bool) :
    (∑ n : ZMod 7, pRT (n, b)) = if b then 1 / 3 else 2 / 3 := by
  have h : (∑ n : ZMod 7, pRT (n, b)) = ((∑ n : ZMod 7, countRT n b : ℕ) : ℝ) / 6 := by
    simp only [pRT, ← Finset.sum_div]
    push_cast
    rfl
  rw [h, countRT_sum_res b]
  cases b <;> norm_num







/-! ## The semiprime channel `N = p·q mod 7 ⟶ unordered type pair` -/






instance (n : ZMod 7) : Decidable (clsB n) := by unfold clsB; infer_instance















/-! ## Which factor is which: exactly zero bits -/


















open CyclicCubic in
theorem solution:
    H Finset.univ (fun b : Bool => ∑ n : ZMod 7, pRT (n, b)) = Real.logb 2 3 - 2 / 3 := by
  have hfun : (fun b : Bool => ∑ n : ZMod 7, pRT (n, b))
      = fun b : Bool => if b = true then (1 : ℝ) / 3 else 2 / 3 := by
    funext b
    rw [pRT_marginal_type b]
  rw [hfun, H_ite_two (fun b : Bool => b = true) (1 / 3) (2 / 3)]
  rw [show (Finset.univ.filter (fun b : Bool => b = true)).card = 1 from by decide,
    show (Finset.univ.filter (fun b : Bool => ¬ b = true)).card = 1 from by decide,
    nlp_one_third, nlp_two_thirds]
  push_cast
  ring
