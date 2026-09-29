-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.exists_key_cost_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:00:49.056749+00:00
-- url     : https://prove2.me/submissions/9e6c6b53-5cea-405f-a61f-afc35e342796

-- Sol generated from Algebra/ScanSchemeDecoding/Optimum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_length_scanList
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_mem_scanList
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_scanList_nodup

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
omit [Fintype β] in
theorem solution{b : β} (hb : (S.fiber b).Nonempty) :
    ∃ x, S.bucket x = b ∧ S.decodeCost x = (S.fiber b).card := by
  classical
  have hlen : (S.scanList b).length = (S.fiber b).card := S.length_scanList b
  have hpos : 0 < (S.scanList b).length := by
    rw [hlen]; exact Finset.card_pos.mpr hb
  have hlt : (S.scanList b).length - 1 < (S.scanList b).length := by omega
  have hmem : (S.scanList b)[(S.scanList b).length - 1] ∈ S.scanList b := List.getElem_mem hlt
  have hbucket : S.bucket (S.scanList b)[(S.scanList b).length - 1] = b := S.mem_scanList.mp hmem
  refine ⟨(S.scanList b)[(S.scanList b).length - 1], hbucket, ?_⟩
  have hidx : (S.scanList b).idxOf (S.scanList b)[(S.scanList b).length - 1]
      = (S.scanList b).length - 1 :=
    List.Nodup.idxOf_getElem (S.scanList_nodup b) _ hlt
  rw [decodeCost, idx, hbucket, hidx]
  omega
