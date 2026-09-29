-- Prove2me | Theorems.Thm_syracuse_two_cycle_eq_one
-- name    : syracuse_two_cycle_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:26:04.590559+00:00
-- url     : https://prove2.me/theorems/c4b30261-5df0-488e-a564-c84b687a77e5
-- title:
--   No nontrivial Syracuse cycle of length $2$
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. Its only positive point of period dividing $2$ is $1$:
--   $$T^{2}(m) = m,\ m>0 \quad\Longrightarrow\quad m = 1 .$$
--
--   Equivalently, the Collatz map has no nontrivial cycle whose accelerated form has length $2$.
--
--   **Mathematical role.** In the accelerated dynamics a Collatz cycle of length $a$ is a solution of $T^{a}(m)=m$, so together with the corresponding statement for $a=1$ this closes the two shortest cases of the cycle problem unconditionally. Writing $x = T(m)$ and multiplying the two step relations $2^{v_1}x = 3m+1$ and $2^{v_2}m = 3x+1$ gives
--   $$\big(2^{\,v_1+v_2} - 9\big)\, m x \;=\; 3m + 3x + 1 .$$
--   The right-hand side is positive, so $2^{v_1+v_2} > 9$; being a power of two it is therefore at least $16$, and the equation forces $7mx \le 3m+3x+1$. Since $mx \ge m+x-1$ for positive $m,x$, this collapses to $m+x \le 2$, leaving only $m=x=1$.
--
--   The point of interest is that no Diophantine input is needed. For a cycle of length $a$ the two general bounds confine the ratio of even to odd steps to $\log_2 3 < K/a \le \log_2(3+1/m)$, and eliminating a given $a$ amounts to showing that this window contains no admissible integer $K$ — a question about rational approximations to $\log_2 3$. For $a \le 2$ the gap between $2^{K}$ and $3^{a}$ is necessarily coarse enough that plain integrality closes it, which is why these cases fall to elementary arithmetic while larger $a$ does not.
--
--   **Formalization note.** No oddness hypothesis is required; a point of period $2$ under $T$ is automatically odd. The statement is period *dividing* $2$: it also covers the fixed-point case, since $T(m)=m$ implies $T^2(m)=m$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_two_cycle_eq_one (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[2] m = m) :
    m = 1 := by sorry
