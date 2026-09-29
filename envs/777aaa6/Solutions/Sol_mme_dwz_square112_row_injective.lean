-- Prove2me | solution 1 for mme_dwz_square112_row_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T08:19:20.685813+00:00
-- url     : https://prove2.me/submissions/e219c3e6-4545-41b6-96c9-85e9d93582cc

import Definitions.Def_mme_dwz_square112_exact_profile_data
open MME.DWZSquare112
set_option autoImplicit false

theorem solution : Function.Injective row := by decide
