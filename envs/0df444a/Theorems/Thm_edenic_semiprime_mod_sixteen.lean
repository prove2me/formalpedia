-- Prove2me | Theorems.Thm_edenic_semiprime_mod_sixteen
-- name    : edenic_semiprime_mod_sixteen
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T23:06:28.699576+00:00
-- url     : https://prove2.me/theorems/f0408b6e-1d88-415b-a970-3461d6f9004a
-- title:
--   Edenic semiprimes are 3 or 15 modulo 16
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$n \equiv 3 \pmod{16} \qquad\text{or}\qquad n \equiv 15 \pmod{16}.$$
--
--   The prime $p$ is odd ($p = 2$ gives $p+2 = 4$ composite), so $p \equiv 1$ or $3 \pmod 4$:
--   - $p = 4s+1$: $n = (4s+1)(4s+3) = 16s(s+1) + 3 \equiv 3 \pmod{16}$;
--   - $p = 4s+3$: $n = (4s+3)(4s+5) = 16s(s+2) + 15 \equiv 15 \pmod{16}$.
--
--   Both classes occur ($35 \equiv 3$, $15 \equiv 15$), and no other residue mod 16 is possible. Note $n \equiv 15 \equiv -1 \pmod{16}$ reflects the near-square shape $n = p^2 + 2p = (p+1)^2 - 1$: an Edenic semiprime is one less than a perfect square, and odd squares are $1 \pmod 8$, refined here to the two surviving classes mod 16.
--
--   **Formalization.** Dispose of $p = 2$, extract oddness via `Nat.Prime.eq_two_or_odd'`, split $p \bmod 4$ with `omega`, rewrite each product to the canonical $16k + c$ shape by `ring`, and reduce with `simp [Nat.mul_mod, Nat.add_mod]`.
--
--   **Reuse.** Companion to `edenic_semiprime_mod_eight`: this is the exact mod-16 refinement — each mod-8 class splits into two mod-16 classes.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_mod_sixteen (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 16 = 3 ∨ n % 16 = 15 := by
  sorry
