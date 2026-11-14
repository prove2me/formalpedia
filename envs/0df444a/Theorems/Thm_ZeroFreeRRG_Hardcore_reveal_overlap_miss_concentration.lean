-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_overlap_miss_concentration
-- name    : ZeroFreeRRG.Hardcore.reveal_overlap_miss_concentration
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:24:30.785844+00:00
-- url     : https://prove2.me/theorems/b7784f26-73a8-4fe6-af6f-6e54e0112b87
-- title:
--   Revealed overlap detects a full overlap deviation
-- statement:
--   For $0<s\le1$ and $0<\eta\le1$, if the full empirical pair overlap differs from the product marginal by more than $\eta$ in some coordinate, the independent Bernoulli($s$) reveal set misses the paper’s revealed-deviation event with probability at most $2e^{-s\eta^2n/12}$. This is the first Bernstein bound in the proof of Lemma 5.6.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, two Bernstein inequalities in the proof of Lemma 5.6.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_RevealOverlap
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.reveal_overlap_miss_concentration (m : Model) (hm : m.Valid)
    (t s η : ℝ) (ht : m.PosParam t) (hs : 0 < s) (hs1 : s ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (n : ℕ) (σ σ' : Fin n → m.Spin)
    (hdev : fullOverlapDeviation m t η σ σ') :
    (∑ U : Finset (Fin n), revealProb s U *
      (if ¬ revealedOverlapH m t s η U (fun v => σ v.1) (fun v => σ' v.1) then 1 else 0))
      ≤ 2*Real.exp (-(s*η^2/12)*n) := by sorry
