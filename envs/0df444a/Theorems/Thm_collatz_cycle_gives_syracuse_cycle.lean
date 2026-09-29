-- Prove2me | Theorems.Thm_collatz_cycle_gives_syracuse_cycle
-- name    : collatz_cycle_gives_syracuse_cycle
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:35:40.242188+00:00
-- url     : https://prove2.me/theorems/f27376f3-b444-482e-b480-9ff2b191e586
-- title:
--   Every classical Collatz cycle contains a Syracuse-periodic point
-- statement:
--   Let $C$ be the classical Collatz map and $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ the accelerated Syracuse map. Every positive cycle of $C$ contains a point which is genuinely periodic for $T$:
--   $$C^{p}(x)=x,\ x>0,\ p\ge1 \quad\Longrightarrow\quad \exists\, z,a,k:\ z>0,\ a>0,\ T^{a}(z)=z,\ C^{k}(x)=z .$$
--
--   **Mathematical role.** This is the transfer principle that makes the accelerated theory applicable to the original problem. Every sharp statement about Collatz cycles — the inequality $3^{a}<2^{K}$, the bound $2^{K}m^{a}\le(3m+1)^{a}$ on a cycle's minimum, the resulting estimate $m \lesssim a\,3^{a-1}$, and the exclusion of short accelerated periods — is a statement about $T$, because $T$ carries the arithmetic of the problem without the intervening halvings. None of it says anything about a hypothetical classical cycle until one knows that such a cycle *contains* a $T$-periodic point. That is what this provides, together with the fact that the point is reached from $x$ by the classical map, so the two cycles genuinely share an orbit.
--
--   The argument is a finiteness one. A classical cycle contains an odd number $y$, at which the accelerated dynamics can start. Every Syracuse iterate of $y$ is again a classical iterate of $x$, since one $T$-step is a run of $C$-steps; and the classical orbit of a periodic point is finite, being determined by the residue of the index modulo $p$. So the sequence $T^{t}(y)$ takes only finitely many values and must repeat: $T^{s}(y)=T^{t}(y)$ for some $s<t$. The point $z=T^{s}(y)$ then satisfies $T^{\,t-s}(z)=z$ with $t-s>0$.
--
--   **What it does and does not give.** Combined with the exclusion of accelerated periods $1$ through $5$, it shows that any positive classical cycle whose accelerated period is at most $5$ must contain $1$, hence is the trivial cycle. It does not bound that accelerated period, so it does not by itself exclude classical cycles; supplying such a bound is the remaining content of the cycle problem.
--
--   **Formalization note.** The conclusion asserts $z$ is reached from $x$ in $k$ classical steps, rather than that $z$ lies in a set, so no orbit set need be defined. The period $a$ produced is positive but not claimed minimal.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map) and Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep

theorem collatz_cycle_gives_syracuse_cycle (x p : ℕ) (hx : 0 < x) (hp : 0 < p)
    (hcyc : collatzStep^[p] x = x) :
    ∃ z a k : ℕ, 0 < z ∧ 0 < a ∧ syracuseStep^[a] z = z ∧ collatzStep^[k] x = z := by sorry
