-- Prove2me | Theorems.Thm_syracuse_small_reaches_one
-- name    : syracuse_small_reaches_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:48:38.950767+00:00
-- url     : https://prove2.me/theorems/686cc205-cac4-4284-b9dd-7afc4bd394ff
-- title:
--   Every odd $m \le 33$ reaches $1$ under the Syracuse map
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. Every odd number up to $33$ reaches $1$ under iteration of $T$:
--   $$m \text{ odd},\ 0 < m \le 33 \quad\Longrightarrow\quad \exists\, k,\ T^{k}(m)=1 .$$
--
--   **Mathematical role.** This is the Collatz conjecture verified on an explicit initial segment, in accelerated form. On its own it is a finite computation, but paired with the fact that a $T$-periodic point reaching $1$ must equal $1$, it acquires uniform force: **no nontrivial $T$-cycle can contain any element at most $33$**, whatever the length of that cycle.
--
--   That is exactly the shape needed by the exclusions of individual accelerated cycle lengths. Each such exclusion bounds a hypothetical cycle below by an explicit threshold $B_a$ and is then left checking small values; the thresholds for the first dozen lengths are
--   $$B_a = 3,\,3,\,7,\,3,\,33,\,7,\,5,\,13,\,7,\,33,\,11,\,7 \qquad (a=1,\dots,12),$$
--   all of them at most $33$. So this single statement supplies the residual half of every one of those arguments at once, replacing a dozen separate hand computations.
--
--   The bound $33$ is not arbitrary: it is the largest threshold occurring among the first twelve lengths, and it is attained at $a=5$ and $a=10$, the lengths where $2^{K}$ sits closest above $3^{a}$ because $8/5$ approximates $\log_2 3$ well.
--
--   **Formalization note.** The orbits involved are short but not trivial: the longest is that of $27$, which takes $41$ accelerated steps and climbs to $3077$ before descending. Oddness is required — the Syracuse map is only the natural accelerated map on odd inputs — and is automatic for any point of a $T$-cycle.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem CollatzMission.collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2, https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_small_reaches_one (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 33) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by sorry
