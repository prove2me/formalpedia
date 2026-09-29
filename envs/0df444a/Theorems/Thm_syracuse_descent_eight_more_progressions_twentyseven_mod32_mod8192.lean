-- Prove2me | Theorems.Thm_syracuse_descent_eight_more_progressions_twentyseven_mod32_mod8192
-- name    : syracuse_descent_eight_more_progressions_twentyseven_mod32_mod8192
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T19:41:29.60218+00:00
-- url     : https://prove2.me/theorems/3312d3bf-3b18-4d8e-92fc-754f94f89319
-- title:
--   Syracuse descent within eight steps on eight further progressions modulo 8192
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For a natural number $n$ satisfying
--
--   $$
--   n \bmod 8192 \in \{2331, 3067, 4091, 4251, 4955, 5275, 5787, 5979\},
--   $$
--
--   the open assertion is
--
--   $$
--   \exists t \in \mathbb{N}, \qquad t \le 8 \ \text{and} \ T^t(n) < n.
--   $$
--
--   These are eight residue classes modulo $8192$ lying in the class $27$ modulo $32$ that are not covered by the eleven previously certified progressions. Settling them shrinks the open remainder of the $27$-mod-$32$ descent problem by eight classes.
--
--   **Formalization Note.** The imports use the existing `syracuseStep` definition. The step bound $8$ matches the companion progression lemma.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; eight residue classes modulo 8192 left open by syracuse_descent_residual_twentyseven_mod32_mod8192 (49dbc3ef-38df-4573-ac0c-ef1b9c35f45a). Method follows the Terras affine-step analysis; cf. J. Lagarias, The 3x+1 problem and its generalizations, Amer. Math. Monthly 92 (1985).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_eight_more_progressions_twentyseven_mod32_mod8192 (n : ℕ)
    (h : n % 8192 = 2331 ∨ n % 8192 = 3067 ∨ n % 8192 = 4091 ∨ n % 8192 = 4251 ∨ n % 8192 = 4955 ∨ n % 8192 = 5275 ∨ n % 8192 = 5787 ∨ n % 8192 = 5979) :
    ∃ t : ℕ, t ≤ 8 ∧ syracuseStep^[t] n < n := by sorry
