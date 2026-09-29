-- Prove2me | Theorems.Thm_collatz_cycle_has_odd
-- name    : collatz_cycle_has_odd
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:28:37.786997+00:00
-- url     : https://prove2.me/theorems/b86ff0d0-d89f-4849-8c04-812782fba740
-- title:
--   Every positive Collatz cycle contains an odd number
-- statement:
--   Let $C$ be the classical Collatz map, $C(n)=n/2$ for even $n$ and $C(n)=3n+1$ for odd $n$. Every positive periodic point of $C$ has an odd number somewhere in its orbit:
--   $$C^{p}(x)=x,\ x>0,\ p\ge 1 \quad\Longrightarrow\quad \exists\, i,\ C^{i}(x) \text{ is odd}.$$
--
--   **Mathematical role.** This is the bridge between the classical map and its accelerated form. The Syracuse map $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ is defined on odd inputs and collapses each ascending step together with the ensuing run of halvings; results about cycles are far easier to state and prove for $T$, since a $T$-cycle carries the arithmetic of the problem without the intervening halvings. To transfer any such result back to the classical map one must first know that a classical cycle meets the odd numbers at all — otherwise there is no point at which to start the accelerated dynamics.
--
--   The reason is immediate once stated: an orbit consisting entirely of even numbers halves at every step, so it strictly decreases, and a strictly decreasing orbit cannot return to its starting point. The hypothesis $x>0$ is essential, since $0$ is a fixed point whose orbit is entirely even.
--
--   **Formalization note.** Oddness is written as $\neg\,\mathrm{Even}$ rather than $\mathrm{Odd}$; over $\mathbb{N}$ the two are equivalent. The index $i$ is unconstrained, though it may always be taken below $p$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_cycle_has_odd (x p : ℕ) (hx : 0 < x) (hp : 0 < p)
    (hcyc : collatzStep^[p] x = x) :
    ∃ i : ℕ, ¬ Even (collatzStep^[i] x) := by sorry
