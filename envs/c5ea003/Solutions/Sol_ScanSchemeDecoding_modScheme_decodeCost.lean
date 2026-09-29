-- Prove2me | solution 1 for ScanSchemeDecoding.modScheme_decodeCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:10:49.206617+00:00
-- url     : https://prove2.me/submissions/1a36afce-e6d7-45db-9e90-1ad01f6c6401

-- Sol generated from Algebra/ScanSchemeDecoding/Optimum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq
import Theorems.Thm_ScanSchemeDecoding_card_range_filter_mod
import Theorems.Thm_ScanSchemeDecoding_sum_triangle_balanced

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



/-- The residue scheme has perfectly balanced buckets. -/
theorem modScheme_fiber_card (N : ℕ) {m : ℕ} (hm : 0 < m) (j : Fin m) :
    ((modScheme N hm).fiber j).card = balancedProfile N m j := by
  classical
  have hfilter : ((modScheme N hm).fiber j)
      = Finset.filter (fun x : Fin N => (x : ℕ) % m = (j : ℕ)) Finset.univ := by
    ext x
    simp [ScanScheme.fiber, modScheme, Fin.ext_iff]
  have hcount := card_range_filter_mod hm j.isLt N
  rw [Finset.card_filter] at hcount
  rw [hfilter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun k => if k % m = (j : ℕ) then 1 else 0) N, hcount]
  rfl




open ScanSchemeDecoding in
theorem solution(N : ℕ) {m : ℕ} (hm : 0 < m) :
    ∑ x, (modScheme N hm).decodeCost x = triangleOpt N m := by
  classical
  rw [ScanScheme.decodeCost_eq]
  have : ∀ j : Fin m, triangle ((modScheme N hm).fiber j).card
      = triangle (balancedProfile N m j) := by
    intro j; rw [modScheme_fiber_card]
  rw [Finset.sum_congr rfl (fun j _ => this j), sum_triangle_balanced hm N]
