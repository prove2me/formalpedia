-- Prove2me | solution 1 for CyclicCubic.H_typeMarginal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:17:38.316839+00:00
-- url     : https://prove2.me/submissions/fe458867-d5ea-4fec-ad0c-91c21ae481e8

-- Sol generated from Applications/CyclicCubicTypeChannel/Entropy.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Entropy
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_LabelEntropyDeficit
import Theorems.Thm_CyclicCubic_H_typeMarginal
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





/-! ## Mutual information of a joint distribution -/


/-! ## Logarithm values -/












/-! ## Numerical bounds on `log₂ 3` -/

theorem log2_three_gt : 1.584 < Real.logb 2 3 := by
  have hnat : (2 : ℕ) ^ 1584 < 3 ^ 1000 := by decide +kernel
  have hr : (2 : ℝ) ^ (1584 : ℕ) < (3 : ℝ) ^ (1000 : ℕ) := by exact_mod_cast hnat
  have h := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hr
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  push_cast at h
  linarith

theorem log2_three_lt : Real.logb 2 3 < 1.585 := by
  have hnat : (3 : ℕ) ^ 1000 < 2 ^ 1585 := by decide +kernel
  have hr : (3 : ℝ) ^ (1000 : ℕ) < (2 : ℝ) ^ (1585 : ℕ) := by exact_mod_cast hnat
  have h := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hr
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  push_cast at h
  linarith

/-! ## The type map -/




/-! ## The single-prime channel `p mod 7 ⟶ type` -/

















/-! ## The semiprime channel `N = p·q mod 7 ⟶ unordered type pair` -/






instance (n : ZMod 7) : Decidable (clsB n) := by unfold clsB; infer_instance















/-! ## Which factor is which: exactly zero bits -/


















open CyclicCubic in
theorem solution:
    0.917 < H Finset.univ (fun b : Bool => ∑ n : ZMod 7, pRT (n, b)) ∧
      H Finset.univ (fun b : Bool => ∑ n : ZMod 7, pRT (n, b)) < 0.919 := by
  rw [H_typeMarginal]
  constructor
  · linarith [log2_three_gt]
  · linarith [log2_three_lt]
