-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_shearer_disc
-- name    : ZeroFreeRRG.Hardcore.hardcore_shearer_disc
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:36:46.065187+00:00
-- url     : https://prove2.me/theorems/c2c49ff0-cc0a-4ceb-9ad6-5c8dbf0183fd
-- title:
--   Hardcore zero-free disk at the Shearer radius
-- statement:
--   Let $G$ be a finite simple graph of maximum degree at most $d\ge3$. Its hardcore independence polynomial is nonzero at every complex fugacity $\lambda$ satisfying $$|\lambda|<\frac{(d-1)^{d-1}}{d^d}.$$ This is the hardcore assertion of Lemma 5.7.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped Classical

theorem ZeroFreeRRG.Hardcore.hardcore_shearer_disc {V : Type} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hd : 3 ≤ d) (hG : ∀ v, G.degree v ≤ d) (z : ℂ)
    (hz : ‖z‖ < ((d:ℝ)-1)^(d-1)/(d:ℝ)^d) : hardcoreZfug G z ≠ 0 := by sorry
