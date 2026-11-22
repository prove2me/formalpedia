-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.supportScore_gt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:53:20.996177+00:00
-- url     : https://prove2.me/submissions/5707b1ab-880b-4b35-a92a-57455e4f00e4

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (support : List (Vec n)) (x : Fin n → ℝ)
    (epsilon : ℝ) (he : epsilon < 1) :
    epsilon < supportScore support x ↔ ∀ u ∈ support, epsilon < dot u x := by
  induction support with
  | nil => simp [supportScore, he]
  | cons u rest ih => simp [supportScore, ih]
end Kourovka.MetabelianEnumeration.ConeVerifier
