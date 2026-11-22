-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ValuationModule.span_eq_half_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:13:29.689236+00:00
-- url     : https://prove2.me/submissions/30f7a230-5786-4bc0-9953-862e375db93c

import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_Kourovka_Modules_ValuationModule
import Theorems.Thm_Kourovka_MetabelianEnumeration_ValuationModule_scalar_replacement

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ValuationModule
variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]
variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]
namespace Kourovka.MetabelianEnumeration.ValuationModule
theorem _root_.solution (χ : Q →+ ℝ) (p : GroupRing Q)
    (hp : ∀ u ∈ p.support, 0 < χ u) (hact : ∀ m : M, p • m = m)
    (s : Set M) : ∀ m ∈ Submodule.span (GroupRing Q) s,
      m ∈ Submodule.span (nonnegativeRing χ) s := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr'⟩ := scalar_replacement χ p hp hact r
    rw [← hr' x]
    exact Submodule.smul_mem _ r' hx
end Kourovka.MetabelianEnumeration.ValuationModule
