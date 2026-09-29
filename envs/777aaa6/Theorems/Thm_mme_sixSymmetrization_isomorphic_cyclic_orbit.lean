-- Prove2me | Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_orbit
-- name    : mme_sixSymmetrization_isomorphic_cyclic_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:44:21.867053+00:00
-- url     : https://prove2.me/theorems/8d4e468a-495c-4213-bb5e-516bad543c49
-- title:
--   Six-symmetrization is invariant along the cyclic mode orbit
-- statement:
--   Let $T$ be a trilinear tensor over a field, and let $c$ cyclically permute its three modes. Then the six-symmetrizations of $T$, $cT$, and $c^2T$ are pairwise isomorphic. In particular,
--
--   $$
--   \operatorname{Six}(cT) \cong \operatorname{Six}(T), \qquad \operatorname{Six}(c^2T) \cong \operatorname{Six}(T).
--   $$
--
--   This orbit-invariance allows results proved after cyclically normalizing a tensor's mode orientation to be transported back to its literal orientation without changing the six-symmetrized tensor up to mutual restriction.
-- source:
--   Formal cyclic-orbit consequence of the six-symmetrization and cyclic-symmetrization definitions used in the matrix-multiplication asymptotic sum inequality framework.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_sixSymmetrization_isomorphic_cyclic_orbit
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
        (sixSymmetrization (TensorObj.permObj cyclicPerm T))
        (sixSymmetrization T) ∧
      TensorObj.Isomorphic
        (sixSymmetrization
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))
        (sixSymmetrization T) := by
  sorry
