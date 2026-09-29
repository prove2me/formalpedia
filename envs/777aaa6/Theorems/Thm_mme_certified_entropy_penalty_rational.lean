-- Prove2me | Theorems.Thm_mme_certified_entropy_penalty_rational
-- name    : mme_certified_entropy_penalty_rational
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T01:41:32.729513+00:00
-- url     : https://prove2.me/theorems/621fb7a3-c8f1-40d9-b1ce-75c4bb09250e
-- title:
--   The entropy penalty is bounded by a purely rational expression
-- statement:
--   The recursive maximum-entropy penalty is bounded by a purely rational expression, with no
--   logarithms at all.
--
--   The Gibbs dual bounds the penalty above by the logarithm of the total reference mass, minus the
--   reference log-moment of the distribution, minus its entropy. The Gibbs bound on the entropy itself
--   involves the very same log-moment, with the opposite sign. Using the same reference in both, the two
--   log-moments cancel exactly, and bounding the remaining logarithm of the total by that total minus
--   one leaves only rational data: the total reference mass, minus two, plus the sum of the squared
--   weights divided by their references.
--
--   So certifying a penalty needs no logarithm constants whatsoever, and the bound is as small as the
--   references are accurate.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_entropy_reference
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_certified_entropy_bounds
import Theorems.Thm_mme_certified_entropy_penalty

open BigOperators MME MME.RegionRate MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_certified_entropy_penalty_rational :
    ∀ {half : ℕ} {parent : Fin 3 → ℕ} (alpha : RecursiveThinSplit.Split half parent → ℚ),
      (∀ c, 0 ≤ alpha c) → ∑ c, alpha c = 1 →
      ∀ E : Fin 3 → Fin (half + 1) → (Fin 4 → ℤ),
      Real.log 2 * entropyPenalty (fun c ↦ ((alpha c : ℚ) : ℝ)) ≤
        (((∑ c : RecursiveThinSplit.Split half parent,
            qvalQ (fun k ↦ ∑ i, E i (c.val i) k)) - 2 +
          ∑ c : RecursiveThinSplit.Split half parent,
            (alpha c) ^ 2 / qvalQ (fun k ↦ ∑ i, E i (c.val i) k) : ℚ) : ℝ) := by sorry
