-- Prove2me | solution 1 for mme_kronPowModeMap_recursive_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:43:57.46029+00:00
-- url     : https://prove2.me/submissions/3d6c545e-4183-44b9-8109-d8752b735a18

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_kron_pow_word_reindex

open MME MME.TensorObj MME.DWZComponentRestriction TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

theorem solution
    {K : Type u} [Field K]
    {T S : TensorObj K 3} (i : Fin 3)
    {I J : Type u}
    (b : Basis I K (T.V i)) (c : Basis J K (S.V i))
    (f : T.V i →ₗ[K] S.V i) (label : I → J)
    (hf : ∀ a, f (b a) = c (label a)) :
    ∀ (n : ℕ) (w : PowIndex I n),
      kronPowModeMap i f n (kronPowModeBasis T i b n w) =
        kronPowModeBasis S i c n
          (PowIndex.ofFun n (fun r ↦ label (PowIndex.get n w r))) := by
  intro n
  induction n with
  | zero =>
      intro w
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      rfl
  | succ n ih =>
      rintro ⟨a, w⟩
      change TensorProduct.map f (kronPowModeMap i f n)
          ((Module.Basis.tensorProduct b (kronPowModeBasis T i b n))
            (a, w)) = _
      rw [Module.Basis.tensorProduct_apply]
      rw [TensorProduct.map_tmul, hf, ih]
      change _ =
        (Module.Basis.tensorProduct c (kronPowModeBasis S i c n))
          (label a,
            PowIndex.ofFun n
              (fun r ↦ label (PowIndex.get n w r)))
      rw [Module.Basis.tensorProduct_apply]
