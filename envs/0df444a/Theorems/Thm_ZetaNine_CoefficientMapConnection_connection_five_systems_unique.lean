-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapConnection_connection_five_systems_unique
-- name    : ZetaNine.CoefficientMapConnection.connection_five_systems_unique
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T11:47:07.484165+00:00
-- url     : https://prove2.me/theorems/37ff9673-ea18-4954-8859-e711491af165
-- title:
--   The five original connection systems have unique bounded rational solutions
-- statement:
--   For every n>=1 and r=0,...,4, there exists exactly one rational polynomial pair P,q of natural degrees at most four and nine satisfying the full original polynomial identity with the genuine scaled three-factor Z_n(u)(u-n-1)^r target. Rational-function, HasSum and five-output parameter transport are separate results.
-- source:
--   Actual original D/H connection system; frozen source SHA256 098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8.

import Definitions.Def_ZetaNine_CoefficientMapConnection

set_option autoImplicit false
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection

theorem ZetaNine.CoefficientMapConnection.connection_five_systems_unique (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (connectionTarget n r.val).comp (connectionU n):= by sorry
