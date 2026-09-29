-- Prove2me | solution 1 for mme_perm_kronPow_mode_equiv_recursive_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:54:06.856117+00:00
-- url     : https://prove2.me/submissions/00121422-92e3-43e7-8a08-3e622a970b21

import Definitions.Def_mme_perm_kronPow_mode_equiv
import Definitions.Def_mme_kron_pow_mode_word_basis

open MME MME.TensorObj MME.DWZComponentRestriction TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (e : Equiv.Perm (Fin 3)) (T : TensorObj K 3) (i : Fin 3)
    {I : Type u} (b : Basis I K (T.V (e.symm i))) :
    ∀ (n : ℕ) (w : PowIndex I n),
      permKronPowModeEquiv e T i n
          (kronPowModeBasis (TensorObj.permObj e T) i b n w) =
        kronPowModeBasis T (e.symm i) b n w := by
  intro n
  induction n with
  | zero =>
      intro w
      have hw : w = PUnit.unit := Subsingleton.elim _ _
      subst w
      rfl
  | succ n ih =>
      rintro ⟨a, w⟩
      change TensorProduct.congr
          (LinearEquiv.refl K (T.V (e.symm i)))
          (permKronPowModeEquiv e T i n)
          ((Module.Basis.tensorProduct b
            (kronPowModeBasis (TensorObj.permObj e T) i b n))
              (a, w)) = _
      rw [Module.Basis.tensorProduct_apply, TensorProduct.congr_tmul, ih]
      change _ =
        (Module.Basis.tensorProduct b
          (kronPowModeBasis T (e.symm i) b n)) (a, w)
      rw [Module.Basis.tensorProduct_apply]
      rfl
