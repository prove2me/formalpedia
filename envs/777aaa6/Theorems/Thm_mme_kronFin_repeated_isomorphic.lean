-- Prove2me | Theorems.Thm_mme_kronFin_repeated_isomorphic
-- name    : mme_kronFin_repeated_isomorphic
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T09:58:53.414974+00:00
-- url     : https://prove2.me/theorems/6aba9fad-8ab2-4173-88b6-a1d9863c9607
-- title:
--   Independent tensor multiplicities multiply exactly
-- statement:
--   A tensor product of repeated tensors is isomorphic to the product tensor repeated by the exact product of its multiplicities, including zero and empty cases. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_toQ_kronFin
open MME MME.TensorObj BigOperators
universe u

theorem mme_kronFin_repeated_isomorphic {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d) (copies : Fin n → ℕ) :
    Isomorphic (kronFin n (fun r => bigAdd (fun _ : Fin (copies r) => T r)))
      (bigAdd (fun _ : Fin (∏ r, copies r) => kronFin n T)) := by sorry
