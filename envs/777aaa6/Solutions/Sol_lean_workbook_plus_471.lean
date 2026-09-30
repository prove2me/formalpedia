-- Prove2me | solution 1 for lean_workbook_plus_471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:14.238637+00:00
-- url     : https://prove2.me/submissions/0c90816d-3d8d-4598-a91d-c5ff31a37389

import Mathlib.Analysis.Complex.Basic

set_option maxRecDepth 100000 in
theorem solution :
  Finset.card (Finset.filter (λ x => 2 ∣ x ∨ 3 ∣ x ∨ 7 ∣ x) (Finset.range 750)) = 536 := by
  decide
