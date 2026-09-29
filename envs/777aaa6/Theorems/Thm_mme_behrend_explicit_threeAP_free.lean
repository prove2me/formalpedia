-- Prove2me | Theorems.Thm_mme_behrend_explicit_threeAP_free
-- name    : mme_behrend_explicit_threeAP_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T15:43:52.072618+00:00
-- url     : https://prove2.me/theorems/cb45e6ba-b86a-4119-a08e-f162c8fbc86b
-- title:
--   An explicit finite Behrend progression-free set
-- statement:
--   For every natural number $N$, there is a set $S\subseteq\{0,\ldots,N-1\}$ containing no nontrivial three-term arithmetic progression and satisfying
--
--   $$
--   |S|\ge N\exp\!\left(-4\sqrt{\log N}\right).
--   $$
--
--   The conclusion exposes the actual finite set, its containment in the required interval, its progression-free property, and the explicit Behrend cardinality bound. It is suitable for quantitative Salem--Spencer hashing arguments in tensor-power laser extractions, where the subexponential loss must remain visible.
-- source:
--   F. A. Behrend, On sets of integers which contain no three terms in arithmetical progression, Proc. Natl. Acad. Sci. USA 32 (1946), 331--332; formal quantitative bound `Behrend.roth_lower_bound` and witness theorem `rothNumberNat_spec` in Mathlib, Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean and Defs.lean.

import Mathlib.Combinatorics.Additive.AP.Three.Behrend

open Real

theorem mme_behrend_explicit_threeAP_free (N : ℕ) :
    ∃ S : Finset ℕ,
      S ⊆ Finset.range N ∧
      ThreeAPFree (S : Set ℕ) ∧
      (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤ (S.card : ℝ) := by sorry
