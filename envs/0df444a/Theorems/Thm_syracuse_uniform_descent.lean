-- Prove2me | Theorems.Thm_syracuse_uniform_descent
-- name    : syracuse_uniform_descent
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-10T19:13:32.155393+00:00
-- url     : https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a
-- title:
--   Terras uniformity: descent transfers across a residue class mod $2^K$
-- statement:
--   Let $T$ be the Syracuse map, $T(n) = (3n+1)/2^{v_2(3n+1)}$. Fix an odd $m'$ and record the exponents stripped along its first $t$ steps: $a_0, \dots, a_{t-1}$, so that
--
--   $$2^{a_i}\, T^{i+1}(m') = 3\,T^{i}(m') + 1 \qquad (i < t).$$
--
--   Write $S = \sum_{i<t} a_i$ for the total number of halvings. Suppose
--
--   - the halvings fit inside the modulus, $S + 1 \le K$;
--   - the orbit contracts, $3^t < 2^{S}$;
--   - the representative descends, $T^t(m') < m'$.
--
--   Then **every** odd $m \ge m'$ congruent to $m'$ modulo $2^K$ satisfies $T^t(m) < m$, using the same number of steps.
--
--   **Why this is the useful form.** Verifying that numbers below a bound descend is normally done one integer at a time, which is why explicit Collatz bounds advance in small increments. This statement replaces that with a single check per *residue class*: one representative certifies an entire infinite arithmetic progression. It is the mechanism behind Terras' density argument, in the form needed to certify descent in bulk.
--
--   **The mathematics.** Two facts combine. First, the exponent stripped at each step is determined modulo a power of two: if $m \equiv m' \pmod{2^K}$ and the first step of $m'$ strips exactly $2^{a}$ with $a + 1 \le K$, then the first step of $m$ strips exactly $2^{a}$ as well, and the images remain congruent modulo $2^{K-a}$ — the budget shrinks by precisely what was stripped. Iterating while the budget lasts shows the two orbits strip identical exponents for all $t$ steps.
--
--   Second, an orbit with prescribed exponents is an exact affine function of its starting point:
--
--   $$2^{S}\, T^{t}(m) = 3^{t} m + c,$$
--
--   where the constant $c$ is built from the exponent sequence alone and so is *shared* across the whole class. Descent $T^t(m) < m$ is then equivalent to $c < (2^{S} - 3^{t})\,m$, whose right-hand side is increasing in $m$ once $2^{S} > 3^{t}$. So the inequality, once checked at the smallest representative, holds for every larger member of the class.
--
--   **Formalization note.** The exponent sequence is supplied as a function $a : \mathbb{N} \to \mathbb{N}$ rather than as a derived quantity, which keeps the statement free of auxiliary definitions: the hypothesis `hstep` both names the exponents and asserts they are the ones the orbit of $m'$ actually strips. The hypothesis $S + 1 \le K$ is what makes the congruence survive all $t$ steps, and it is sharp — one bit of headroom is needed at every stage to pin the next valuation.
-- source:
--   R. Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252 (the coefficient-stopping-time / uniformity argument). The affine form of a Syracuse orbit with prescribed 2-adic exponents is classical; this is the version needed to certify descent for an entire residue class from a single representative.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_uniform_descent (a : ℕ → ℕ) (m m' K t : ℕ)
    (hm : Odd m) (hm' : Odd m')
    (hcong : m ≡ m' [MOD 2 ^ K])
    (hstep : ∀ i < t, 2 ^ (a i) * (syracuseStep^[i + 1] m') = 3 * (syracuseStep^[i] m') + 1)
    (hbudget : (∑ i ∈ Finset.range t, a i) + 1 ≤ K)
    (hgt : 3 ^ t < 2 ^ (∑ i ∈ Finset.range t, a i))
    (hdesc : syracuseStep^[t] m' < m')
    (hle : m' ≤ m) :
    syracuseStep^[t] m < m := by sorry
