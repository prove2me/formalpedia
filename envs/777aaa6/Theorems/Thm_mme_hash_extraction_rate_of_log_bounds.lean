-- Prove2me | Theorems.Thm_mme_hash_extraction_rate_of_log_bounds
-- name    : mme_hash_extraction_rate_of_log_bounds
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:46:08.059898+00:00
-- url     : https://prove2.me/theorems/0fb41736-cad3-4343-8838-864ffa396286
-- title:
--   Finite hash-extraction rates from logarithmic bounds
-- statement:
--   Let $D$ be finite hash-extraction data, with positive factor lower bounds $L_j$, repair-copy count $r>0$, and matrix volume $M=abc>0$. Let $\tau,c,w$ be real numbers with $c\ge0$. If
--   $$c\le\sum_j\log L_j-\log r,\qquad w\le\tau\log M,$$
--   then the certified rate satisfies
--   $$\operatorname{rate}_D(\tau)\ge e^{c+w}(1-e^{-c}).$$
--   The factor $1-e^{-c}$ retains the subtraction of one in the definition of the certified copy count. The result holds for every real $\tau$.
-- source:
--   Exact certified copy-count formula and exponential/logarithmic inequalities.

import Definitions.Def_mme_hash_extraction_certificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MME MME.HashExtraction Filter
open scoped BigOperators Topology
set_option autoImplicit false

theorem mme_hash_extraction_rate_of_log_bounds
    (D : Data) (tau c w : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ j, 0 < (D.hash j).lower)
    (hvolume : 0 < D.a * D.b * D.c)
    (hcopies : c ≤ (∑ j, Real.log (D.hash j).lower) - Real.log D.repairCopies)
    (hweight : w ≤ tau * Real.log ((D.a * D.b * D.c : ℕ) : ℝ)) :
    Real.exp (c + w) * (1 - Real.exp (-c)) ≤ D.rate tau := by sorry
