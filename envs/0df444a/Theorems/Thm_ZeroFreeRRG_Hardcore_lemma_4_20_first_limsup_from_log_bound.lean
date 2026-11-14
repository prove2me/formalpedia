-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_first_limsup_from_log_bound
-- name    : ZeroFreeRRG.Hardcore.lemma_4_20_first_limsup_from_log_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:58:52.877233+00:00
-- url     : https://prove2.me/theorems/100354d9-5307-4c2b-a061-c7ff59d5d8a8
-- title:
--   The first likelihood limsup inequality from the first-moment bound
-- statement:
--   For either positive-parameter model, the logarithmic first-moment bound of Lemma 4.20 implies the first limsup inequality in equation (29).
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31, Lemma 4.20, equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter Topology MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.lemma_4_20_first_limsup_from_log_bound (m : Model) (hm : m.Valid) (d : ℕ) (t s : ℝ) (ht : m.PosParam t)
    (hlog : ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, Even (n*d) →
      |Real.log (an m d n t)| ≤ C*Real.log (n+1)) :
    limsup (fun n : ℕ => (((1 : ℝ) / n *
        plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) : ℝ) : EReal))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}) ≤
      limsup (fun n : ℕ => (((1 : ℝ) / n *
        plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U) : ℝ) : EReal))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n*d)}) := by sorry
