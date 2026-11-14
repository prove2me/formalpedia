-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_bethe_dirac_zero
-- name    : ZeroFreeRRG.Hardcore.hardcore_bethe_dirac_zero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:24:01.244195+00:00
-- url     : https://prove2.me/theorems/cefa2435-4e74-4afb-abb2-d15fe779e8ac
-- title:
--   Hardcore Bethe functional vanishes at the constant cavity law
-- statement:
--   For any degree $d$ and $0<\alpha<1/2$, the hardcore Bethe functional at the point mass on its stationary cavity message is zero.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Definition 2.7 and Lemma 4.17.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_bethe_dirac_zero (d : ℕ) (α : ℝ) (ha : 0 < α) (ha1 : α < 1/2) :
    betheK .hardcore α d (diracPi .hardcore α) = 0 := by sorry
