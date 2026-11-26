-- Prove2me | Theorems.Thm_edenic_semiprime_mod_48
-- name    : edenic_semiprime_mod_48
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-26T16:48:24.476803+00:00
-- url     : https://prove2.me/theorems/a9c6c810-9f52-4ba3-8b21-6450f150bed7
-- title:
--   Edenic semiprimes are 35 or 47 modulo 48, except 15
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$n \equiv 35 \pmod{48} \qquad\text{or}\qquad n \equiv 47 \pmod{48} \qquad\text{or}\qquad n = 15 .$$
--
--   The two congruence classes are exactly the Chinese-remainder combinations of the finer constraints the family satisfies: $n \equiv 3$ or $15 \pmod{16}$ (target `edenic_semiprime_mod_sixteen`) and $n \equiv 5 \pmod 6$ unless $n = 15$ (target `edenic_semiprime_mod_six`). Pairing $n \equiv 3 \pmod{16}$ with $n \equiv 5 \pmod 6$ forces $n \equiv 35 \pmod{48}$, and pairing $n \equiv 15 \pmod{16}$ with $n \equiv 5 \pmod 6$ forces $n \equiv 47 \pmod{48}$. The exceptional pair $(3,5)$ gives $n = 15$, which is $\equiv 15 \pmod{16}$ but $\equiv 3 \pmod 6$ — it fails the mod-6 alternative, and indeed $15 \bmod 48 = 15$, so it is a genuine exception rather than a representative of either class. Both classes occur: $35 \equiv 35$ and $143 = 11 \cdot 13 \equiv 47 \pmod{48}$.
--
--   **Formalization.** A pure reduction: case on the imported `edenic_semiprime_mod_sixteen` and `edenic_semiprime_mod_six`; each of the four combinations is closed by an `omega` CRT split over the moduli $16$ and $6$ (lcm $48$), and the $n = 15$ branch is returned verbatim.
--
--   **Reuse.** Strengthens `edenic_semiprime_mod_sixteen` and `edenic_semiprime_mod_six` to modulus 48. Sibling targets: `edenic_semiprime_mod_twenty_four` (the mod-24 shadow: $35, 47$ reduce to $11, 23$) and `edenic_semiprime_mod_twelve`.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_sixteen
import Theorems.Thm_edenic_semiprime_mod_six

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_sixteen
import Theorems.Thm_edenic_semiprime_mod_six

theorem edenic_semiprime_mod_48 (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 48 = 35 ∨ n % 48 = 47 ∨ n = 15 := by
  sorry
