-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.isCompact_cubeSphere
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:53:25.24519+00:00
-- url     : https://prove2.me/submissions/240ee585-3abd-468f-b6ea-93895558e56e

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution (n : ℕ) : IsCompact {x : Fin n → ℝ | CubeSphere x} := by
  have hface : IsClosed {x : Fin n → ℝ | ∃ i, x i = -1 ∨ x i = 1} := by
    have h := isClosed_iUnion_of_finite (fun i : Fin n =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const) :
      ∀ i : Fin n, IsClosed ({x : Fin n → ℝ | x i = -1} ∪ {x | x i = 1}))
    convert h using 1
    ext x
    simp
  have hcube : IsCompact (Set.Icc (-1 : Fin n → ℝ) 1) := isCompact_Icc
  convert hcube.inter_right hface using 1
  ext x
  simp only [Set.mem_setOf_eq, CubeSphere, Set.mem_inter_iff, Set.mem_Icc,
    Pi.le_def, Pi.neg_apply, Pi.one_apply]
  aesop
end Kourovka.MetabelianEnumeration.ConeVerifier
