-- Prove2me | Theorems.Thm_edenic_semiprime_mod_twenty_four
-- name    : edenic_semiprime_mod_twenty_four
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-26T16:48:11.809562+00:00
-- url     : https://prove2.me/theorems/3614f0a8-f997-5591-b355-fddbfe16f9b8
-- title:
--   Edenic semiprimes are 11 or 23 modulo 24, except 15
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$n \equiv 11 \pmod{24} \qquad\text{or}\qquad n \equiv 23 \pmod{24} \qquad\text{or}\qquad n = 15 .$$
--
--   This is the modulus-24 Chinese remainder of $n \equiv 3$ or $7 \pmod 8$ (target `edenic_semiprime_mod_eight`) with $n \equiv 5 \pmod 6$ or $n = 15$ (target `edenic_semiprime_mod_six`): the pairing $(3 \bmod 8,\ 5 \bmod 6)$ solves to $n \equiv 11 \pmod{24}$ and the pairing $(7 \bmod 8,\ 5 \bmod 6)$ to $n \equiv 23 \pmod{24}$. Both classes genuinely occur — $35 \equiv 11$ and $143 \equiv 23 \pmod{24}$ — and the exception is again the pair $(3,5)$: $15 \equiv 7 \pmod 8$ but $15 \equiv 3 \ne 5 \pmod 6$, so it takes the $n = 15$ branch (and $15 \bmod 24 = 15$).
--
--   **Formalization.** Case on the imported `edenic_semiprime_mod_eight` and `edenic_semiprime_mod_six`; each of the four combinations closes by an `omega` CRT split over the moduli $8$ and $6$ (lcm $24$), with the $n = 15$ branch passed through verbatim.
--
--   **Reuse.** The modulus-24 intermediate between `edenic_semiprime_mod_twelve` and `edenic_semiprime_mod_48`: reducing the classes $35, 47$ of the latter modulo $24$ gives exactly $11, 23$.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_eight
import Theorems.Thm_edenic_semiprime_mod_six

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_eight
import Theorems.Thm_edenic_semiprime_mod_six

theorem edenic_semiprime_mod_twenty_four (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 24 = 11 ∨ n % 24 = 23 ∨ n = 15 := by
  sorry
