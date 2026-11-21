-- Prove2me | solution 1 for Kourovka.CentralPeriod.exists_iterate_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:30.177609+00:00
-- url     : https://prove2.me/submissions/4d3dc8dd-efe8-4d10-ac54-c88ad3f41aa7

import Definitions.Def_Kourovka_AbelianWeight
import Definitions.Def_Kourovka_FinitePaths
import Definitions.Def_Kourovka_CentralPeriod
import Theorems.Thm_Kourovka_CentralPeriod_multiples_quotient_finite
import Theorems.Thm_Kourovka_CentralPeriod_quotientMap_surjective
import Theorems.Thm_Kourovka_CentralPeriod_quotientMap_iterate
import Theorems.Thm_Kourovka_CentralPeriod_exists_identity_iterate

set_option autoImplicit true
open Kourovka Kourovka.CentralPeriod
variable (M : Type*) [AddCommGroup M]
namespace Kourovka.CentralPeriod
theorem _root_.solution [Module.Finite ℤ M] (f : M →ₗ[ℤ] M)
    (hf : Function.Surjective f) (d : ℤ) (hd : d ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : M, ∃ y : M, f^[n] x - x = d • y := by
  letI := multiples_quotient_finite M d hd
  obtain ⟨n, hn, he⟩ := exists_identity_iterate (quotientMap M f d)
    (quotientMap_surjective M f hf d)
  refine ⟨n, hn, ?_⟩
  intro x
  have hq := congrFun he ((multiples M d).mkQ x)
  rw [quotientMap_iterate] at hq
  have hz : (multiples M d).mkQ (f^[n] x - x) = 0 := by
    rw [map_sub, hq]
    exact sub_self _
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  exact ⟨y, hy.symm⟩
end Kourovka.CentralPeriod
