-- Prove2me | Theorems.Thm_mme_cyclicSymmetrization_isomorphic_cyclic_orbit
-- name    : mme_cyclicSymmetrization_isomorphic_cyclic_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:18:34.030374+00:00
-- url     : https://prove2.me/theorems/30b54cd5-31eb-49ba-a8d9-b8b55d87ce06
-- title:
--   Cyclic symmetrization is invariant under cyclic mode rotation
-- statement:
--   For every order-three tensor $T$, cyclic symmetrization is unchanged up to tensor isomorphism when $T$ is first rotated by either nontrivial element of the cyclic group on its three modes. Concretely, both $\operatorname{cyc}(\sigma T)$ and $\operatorname{cyc}(\sigma^2 T)$ are isomorphic to $\operatorname{cyc}(T)$. This lets cyclic laser-method values be transported freely among the three oriented representatives of one cyclic orbit.
-- source:
--   Cyclic-symmetrization invariance used throughout the laser method; see A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 3 and the cyclic factors in Lemma 5.1, pp. 354--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Mathlib.Tactic
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_cyclicSymmetrization_isomorphic_cyclic_orbit
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
        (cyclicSymmetrization (TensorObj.permObj cyclicPerm T))
        (cyclicSymmetrization T) ∧
      TensorObj.Isomorphic
        (cyclicSymmetrization
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))
        (cyclicSymmetrization T) := by
  sorry
