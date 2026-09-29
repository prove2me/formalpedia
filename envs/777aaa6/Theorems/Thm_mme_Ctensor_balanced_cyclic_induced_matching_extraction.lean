-- Prove2me | Theorems.Thm_mme_Ctensor_balanced_cyclic_induced_matching_extraction
-- name    : mme_Ctensor_balanced_cyclic_induced_matching_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:22:30.960307+00:00
-- url     : https://prove2.me/theorems/65550c81-ef81-4111-84ba-86f3351a763a
-- title:
--   Finite balanced induced-matching extraction from a cyclic C-tensor
-- statement:
--   Let $T$ be a C-tensor over $\langle1,H,1\rangle$ with $H>0$, and suppose all component matrix products have common volume $v$. For a nonnegative integer $m$, put $R=Hm$, and let $W$ be the number of length-$R$ words over the $H$ component labels in which every label occurs exactly $m$ times. Then the $R$-th power of the cyclic symmetrization restricts to a direct sum of $k$ concrete matrix-multiplication tensors satisfying
--
--   $$
--   k\ge W^2\exp\bigl(-100\sqrt{\log(W+1)}\bigr),
--   $$
--
--   and every surviving summand has volume $v^{3R}$.
--
--   The construction first zeros each cyclic orientation to the balanced type class. Its coarse support is the matrix-multiplication support on the $W$ balanced words. Applying a Behrend induced matching makes the selected blocks disjoint in every mode. Component isomorphisms are applied only after this pruning, so no simultaneous identification on the shared C-tensor mode is assumed.
-- source:
--   Strassen C-tensor type restriction and Salem--Spencer/Behrend induced matching, as used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 271--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_CW_coupled_value

open MME BigOperators Filter

universe u

theorem mme_Ctensor_balanced_cyclic_induced_matching_extraction
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (hH : 0 < H) (m : ℕ) :
    let R : ℕ := H * m
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m}
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        ((cyclicSymmetrization T).kronPow R) ∧
      ((W : ℝ) ^ 2 *
          Real.exp
            (-100 * Real.sqrt
              (Real.log (((W + 1 : ℕ) : ℝ))))) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = volume ^ (3 * R)) := by
  sorry
