-- Prove2me | Theorems.Thm_mme_Ctensor_outer_family_double_balanced_extraction
-- name    : mme_Ctensor_outer_family_double_balanced_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:58:05.145537+00:00
-- url     : https://prove2.me/theorems/6685b5b0-4c4e-4bd6-8bef-1d8a1fbb5bba
-- title:
--   Double-balanced finite extraction for a disjoint outer family of C-tensors
-- statement:
--   Let $T$ restrict to a direct sum of $A>0$ modewise-disjoint C-tensors, each over $\langle 1,H,1\rangle$ with $H>0$ and common component volume $v$. Put $n=A^3$, $r=Hm$, and $R=nr$. Let $W_{\mathrm{out}}$ be the number of length-$R$ words on $n$ ordered outer triples in which every triple occurs $r$ times, and let $W_{\mathrm{in}}$ be the number of length-$r$ words on $H$ labels in which every label occurs $m$ times. Then the $R$-th tensor power of the cyclic symmetrization of $T$ restricts to a direct sum of $k$ matrix-multiplication tensors such that
--
--   $$
--   W_{\mathrm{out}}\left(W_{\mathrm{in}}^2 e^{-100\sqrt{\log(W_{\mathrm{in}}+1)}}\right)^n\le k.
--   $$
--
--   Every surviving summand has dimension product $v^{3R}$. This is the finite structural step in the outer-family C-tensor argument: the outer balance is over ordered triples of family members, while each outer block uses an independent balanced inner extraction. No asymptotic estimate for either multinomial count is included in this theorem.
-- source:
--   V. Strassen's C-tensor value method and its use in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271–272, especially the cyclic three-factor construction and deletion to disjoint matrix products; https://doi.org/10.1016/S0747-7171(08)80013-2. The explicit square-root-of-log matching envelope is inherited from the Prove2Me balanced cyclic C-tensor extraction theorem mme_Ctensor_three_balanced_cyclic_induced_matching_extraction.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

theorem mme_Ctensor_outer_family_double_balanced_extraction
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hA : 0 < A) (hH : 0 < H) (m : ℕ) :
    let n : ℕ := A ^ 3
    let r : ℕ := H * m
    let R : ℕ := n * r
    let Wouter : ℕ :=
      Nat.card
        {w : Fin R → Fin n // ∀ p,
          Fintype.card {j // w j = p} = r}
    let Winner : ℕ :=
      Nat.card
        {w : Fin r → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m}
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        ((cyclicSymmetrization T).kronPow R) ∧
      (Wouter : ℝ) *
          (((Winner : ℝ) ^ 2 *
              Real.exp
                (-100 * Real.sqrt
                  (Real.log (((Winner + 1 : ℕ) : ℝ))))) ^ n) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = volume ^ (3 * R)) := by
  sorry
