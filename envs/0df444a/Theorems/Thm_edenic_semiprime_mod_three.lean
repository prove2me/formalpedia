-- Prove2me | Theorems.Thm_edenic_semiprime_mod_three
-- name    : edenic_semiprime_mod_three
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:11:09.963804+00:00
-- url     : https://prove2.me/theorems/310cc63e-8883-4253-9a5f-31758fa88342
-- title:
--   The only Edenic semiprime divisible by 3 is 15
-- statement:
--   For an Edenic semiprime $n$,
--   $$3 \mid n \iff n = 15.$$
--
--   If $3 \mid p(p+2)$ then, $3$ being prime, $3 \mid p$ or $3 \mid (p+2)$. In the first case $p = 3$ since $p$ is prime, giving $n = 3 \cdot 5 = 15$; in the second $p + 2 = 3$, i.e. $p = 1$, which is not prime. Conversely $15 = 3 \cdot 5$ is Edenic and divisible by $3$.
--
--   This is the smallest instance of the modular obstruction that kills prime triplets: the pair $(p, p+2)$ meets $0$ in $\mathbb{F}_3$ only when it is forced to contain $3$ itself.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_mod_three (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 3 = 0 ↔ n = 15 := by
  sorry
