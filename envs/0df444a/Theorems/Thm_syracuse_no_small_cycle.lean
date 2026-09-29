-- Prove2me | Theorems.Thm_syracuse_no_small_cycle
-- name    : syracuse_no_small_cycle
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:53:47.837902+00:00
-- url     : https://prove2.me/theorems/f2ae2367-c0d1-487d-b130-29f6669676db
-- title:
--   No nontrivial Syracuse cycle contains an element $\le 33$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. No nontrivial $T$-cycle contains a small element:
--   $$T^{a}(z)=z,\ a\ge1,\ 0<z\le 33 \quad\Longrightarrow\quad z=1 .$$
--
--   **Mathematical role.** The length $a$ is completely unconstrained: this excludes small cycle elements at *every* period simultaneously, not one period at a time. It is the combination of two facts — that the odd numbers up to $33$ all reach $1$ under $T$, and that a periodic point reaching $1$ must equal $1$ — and it is the form in which those facts are actually used.
--
--   Its purpose is to discharge the residual half of every individual cycle-length exclusion. Each such argument bounds a hypothetical cycle below by an explicit threshold $B_a$, obtained by comparing $2^{K}$ with $3^{a}$, and is then left with a finite check on the values beneath it. For the first twelve lengths those thresholds are
--   $$B_a = 3,\,3,\,7,\,3,\,33,\,7,\,5,\,13,\,7,\,33,\,11,\,7 \qquad (a=1,\dots,12),$$
--   all at most $33$. So for every one of those lengths the check is now immediate, and no separate small-case analysis is needed. Transferred through the correspondence between classical and accelerated cycles, the same statement constrains cycles of the original Collatz map.
--
--   **What remains.** This supplies only the residual half. The other half, the lower bound $B_a$ on a cycle's elements, is proved separately for each length, and the thresholds grow without bound along the lengths for which $2^{K}$ approaches $3^{a}$ closely — the convergents of $\log_2 3$. So the cutoff $33$ can be raised by further verification, but no fixed cutoff serves all lengths.
--
--   **Formalization note.** No oddness hypothesis appears: a point of period $a \ge 1$ under $T$ is automatically odd, since $T$ returns an odd part. The period is not assumed minimal.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_small_cycle (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 33)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry
