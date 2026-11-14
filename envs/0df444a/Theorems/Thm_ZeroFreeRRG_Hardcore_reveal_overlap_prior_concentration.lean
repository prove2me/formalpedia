-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_overlap_prior_concentration
-- name    : ZeroFreeRRG.Hardcore.reveal_overlap_prior_concentration
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:24:29.750633+00:00
-- url     : https://prove2.me/theorems/1d194ddf-4167-4a7f-b29d-820c261710a5
-- title:
--   Product-prior concentration of the revealed overlap
-- statement:
--   For $0<s\le1$ and $0<\eta\le1$, the probability of the paper’s revealed-deviation event under an independent Bernoulli reveal set and two independent product-prior spin assignments is at most $2|\Omega|^2 e^{-s\eta^2 n/12}$. This is the second Bernstein bound in the proof of Lemma 5.6.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, two Bernstein inequalities in the proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_RevealOverlap
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.reveal_overlap_prior_concentration (m : Model) (hm : m.Valid)
    (t s η : ℝ) (ht : m.PosParam t) (hs : 0 < s) (hs1 : s ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (n : ℕ) :
    (∑ U : Finset (Fin n), revealProb s U *
      ∑ y : ({v : Fin n // v ∈ U} → m.Spin), ∑ y' : ({v : Fin n // v ∈ U} → m.Spin),
        if revealedOverlapH m t s η U y y' then
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y v)) *
          (∏ v : {v : Fin n // v ∈ U}, m.pi t (y' v)) else 0)
      ≤ 2*(Fintype.card m.Spin : ℝ)^2*Real.exp (-(s*η^2/12)*n) := by sorry
