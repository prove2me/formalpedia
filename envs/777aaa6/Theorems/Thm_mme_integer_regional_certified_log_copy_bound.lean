-- Prove2me | Theorems.Thm_mme_integer_regional_certified_log_copy_bound
-- name    : mme_integer_regional_certified_log_copy_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T20:04:03.159571+00:00
-- url     : https://prove2.me/theorems/bf638306-4e7b-4c23-a01b-712742713b96
-- title:
--   Explicit log budget guarantees integer regional copies
-- statement:
--   For every actual integer regional extraction step D and every nonnegative real a, if a is at most D.certifiedLogCopies, then exp(a) is at most the integer number D.entropyCopies of guaranteed repaired copies. The proof pays for both natural-number rounding and division by the repair multiplicity; no copy-count hypothesis is assumed.
-- source:
--   New finite-loss lemma for the More Asymmetry numerical instantiation, derived from the proved explicit entropy-copy formula.

import Definitions.Def_mme_regional_certified_log_copy_bound
import Mathlib
open BigOperators MME MME.RegionRate MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_integer_regional_certified_log_copy_bound {ell M : ℕ} {P : ProfiledCW.Predicate M}
    (D : IntegerStep ell M P) (a : ℝ) (ha : 0 ≤ a)
    (hbudget : a ≤ D.certifiedLogCopies) :
    Real.exp a ≤ (D.entropyCopies : ℝ) := by sorry
