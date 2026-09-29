-- Prove2me | solution 1 for lean_workbook_plus_20954
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:42.919744+00:00
-- url     : https://prove2.me/submissions/7dd9c1c2-3ad9-40fb-a7ae-165e4757ed92

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (A B C: Type) (f : B → C) (g : A → B) (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (f ∘ g) := by
  exact hf.comp hg
