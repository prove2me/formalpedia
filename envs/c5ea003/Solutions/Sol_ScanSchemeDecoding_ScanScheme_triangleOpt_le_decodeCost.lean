-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.triangleOpt_le_decodeCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:06:53.245548+00:00
-- url     : https://prove2.me/submissions/339d7a32-d2c3-4f01-932b-5d216baa5b32

-- Sol generated from Algebra/ScanSchemeDecoding/Optimum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_sum_fiber_card
import Theorems.Thm_ScanSchemeDecoding_sum_triangle_ge

/-!
# The exact optimum of a scan scheme, and the pigeonhole failure analysis

Combining the exact cost accounting of `Algebra.ScanSchemeDecoding.Core` with the
exact pigeonhole optimum of `Algebra.ScanSchemeDecoding.Triangle` we obtain:

* `ScanSchemeDecoding.ScanScheme.triangleOpt_le_decodeCost` — **every** scan scheme on
  `N` keys with `m` bucket labels costs at least `triangleOpt N m`;
* `ScanSchemeDecoding.modScheme_decodeCost` — the residue scheme `x ↦ x % m` costs
  *exactly* `triangleOpt N m`;
* `ScanSchemeDecoding.scan_optimum` — hence `triangleOpt N m` is the least achievable
  total cost (`IsLeast`), an exact optimum rather than a bound;
* `ScanSchemeDecoding.ScanScheme.exists_costly_key` — the failure analysis: some key
  always costs at least the average bucket size, `N ≤ m * decodeCost x`;
* `ScanSchemeDecoding.ScanScheme.two_mul_decodeCost_ge` — the averaged `ε`-form.
-/

open ScanSchemeDecoding

open Finset

open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)






/-! ### The residue scheme attains the optimum -/







open ScanSchemeDecoding.ScanScheme in
theorem solution(hβ : 0 < Fintype.card β) :
    triangleOpt (Fintype.card α) (Fintype.card β) ≤ ∑ x, S.decodeCost x := by
  classical
  set m := Fintype.card β with hm
  let e : β ≃ Fin m := Fintype.equivFin β
  have hsum : ∑ i : Fin m, (S.fiber (e.symm i)).card = Fintype.card α := by
    rw [Equiv.sum_comp e.symm (fun b => (S.fiber b).card)]
    exact S.sum_fiber_card
  have hbound := sum_triangle_ge hβ (fun i => (S.fiber (e.symm i)).card) (Fintype.card α) hsum
  have htri : ∑ i : Fin m, triangle (S.fiber (e.symm i)).card
      = ∑ b, triangle (S.fiber b).card :=
    Equiv.sum_comp e.symm (fun b => triangle (S.fiber b).card)
  rw [htri] at hbound
  rw [S.decodeCost_eq]
  exact hbound
