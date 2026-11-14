-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_matching_nonempty_even
-- name    : ZeroFreeRRG.Hardcore.matching_nonempty_even
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:19:54.231357+00:00
-- url     : https://prove2.me/theorems/8e590b20-d565-4f20-876d-0ec1b181bea6
-- title:
--   Admissible configuration-model matching spaces are nonempty
-- statement:
--   If the number $nd$ of configuration-model half-edges is even, then there exists a perfect matching of those half-edges, including the empty matching when $nd=0$.
-- source:
--   Auxiliary configuration-model fact for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Definition 2.1 and §4.3.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
set_option autoImplicit false
open AFIsingKS

theorem ZeroFreeRRG.Hardcore.matching_nonempty_even (n d : ℕ) (he : Even (n*d)) : Nonempty (Matching n d) := by sorry
