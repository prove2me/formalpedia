-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_small_disc
-- name    : ZeroFreeRRG.Hardcore.hardcore_small_disc
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:04:51.169029+00:00
-- url     : https://prove2.me/theorems/5f38872a-04f5-4909-a005-a121483ceb98
-- title:
--   A uniform zero-free disc for the hardcore model
-- statement:
--   Let $G$ be a finite simple graph of maximum degree at most $d\ge1$, and let $Z_G(\lambda)$ be its independent-set polynomial. Then
--
--   $$Z_G(\lambda)\ne0\quad\text{whenever}\quad |\lambda|\le\frac1{d+1}\left(1-\frac1{d+1}\right)^d.$$
--
--   This explicit zero-free disc is a weaker bound than the sharp bound recalled in Lemma 5.7, but is already sufficient for a uniform neighborhood of the hardcore independent-spin endpoint.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Lemma 5.7, printed p. 40; weaker explicit bound derived from the asymmetric local lemma.

import Definitions.Def_ZeroFreeRRG_Hardcore_Models
open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- A weaker explicit zero-free disc sufficient for the independent-spin endpoint. -/
theorem hardcore_small_disc {V : Type} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hd : 1 ≤ d) (hG : ∀ v, G.degree v ≤ d) (z : ℂ)
    (hz : ‖z‖ ≤ (1 / ((d:ℝ)+1)) * (1 - 1 / ((d:ℝ)+1))^d) :
    hardcoreZfug G z ≠ 0 := by sorry
end ZeroFreeRRG.Hardcore
