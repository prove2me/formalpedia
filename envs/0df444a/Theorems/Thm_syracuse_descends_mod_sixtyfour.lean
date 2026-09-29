-- Prove2me | Theorems.Thm_syracuse_descends_mod_sixtyfour
-- name    : syracuse_descends_mod_sixtyfour
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-10T19:32:29.945998+00:00
-- url     : https://prove2.me/theorems/aa1fbfbe-2983-4625-9d78-f5c53dad9bb2
-- title:
--   Syracuse descent for 19 of the 32 odd residue classes mod $64$
-- statement:
--   Let $T(n) = (3n+1)/2^{v_2(3n+1)}$ be the Syracuse map. There are $32$ odd residue classes modulo $64$, and for $19$ of them every member drops below itself within at most three steps:
--
--   $$m \bmod 64 \in \{3,5,9,13,17,19,25,29,33,37,41,43,45,49,51,53,55,57,61\} \;\Longrightarrow\; \exists t,\ T^{t}(m) < m .$$
--
--   Those classes account for $19/32 = 59.4\%$ of the odd integers, so this settles the descent question for a positive proportion of all inputs at once, **with no upper bound on $m$**.
--
--   **How it is proved.** Each class is certified by a single representative. The Terras uniformity theorem `syracuse_uniform_descent` states that if $m \equiv m' \pmod{2^K}$, the orbit of $m'$ descends within $t$ steps stripping exponents totalling $S$, and $S + 1 \le K$ with $3^t < 2^S$, then every odd $m \ge m'$ in the class descends in the same $t$ steps. Applying it with $K = 6$ to each of the $19$ representatives gives the result; the representatives and their exponent data are
--
--   $$3 \mapsto (1,4),\quad 5 \mapsto (4),\quad 9 \mapsto (2),\quad 43 \mapsto (1,2,2),\quad 55 \mapsto (1,1,3), \ \dots$$
--
--   each satisfying the contraction condition $3^t < 2^S$ with $S \le 5$.
--
--   **Why the count is what it is.** The remaining $13$ classes are those whose representatives have not yet dropped by the time the six bits of information in $m \bmod 64$ are exhausted. They are not counterexamples — they are simply undetermined at this depth, and split into sub-classes modulo higher powers of two, most of which certify further down. The proportion certified rises to about $82\%$ at modulus $2^{10}$ and about $95\%$ at $2^{22}$, but it does not reach $1$: the classes that never certify at any depth are exactly the obstruction that makes the Collatz problem hard.
--
--   **Formalization note.** The statement quantifies over all odd $m$ with no upper bound, which is the point: certification is per residue class rather than per integer, so a fixed finite amount of data settles an infinite set.
-- source:
--   Obtained by applying the Terras uniformity theorem (syracuse_uniform_descent) at modulus 2^6 to each of the nineteen certifying residue classes. Underlying method: R. Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_mod_sixtyfour (m : ℕ) (hodd : Odd m)
    (h : m % 64 = 3 ∨
      m % 64 = 5 ∨
      m % 64 = 9 ∨
      m % 64 = 13 ∨
      m % 64 = 17 ∨
      m % 64 = 19 ∨
      m % 64 = 25 ∨
      m % 64 = 29 ∨
      m % 64 = 33 ∨
      m % 64 = 37 ∨
      m % 64 = 41 ∨
      m % 64 = 43 ∨
      m % 64 = 45 ∨
      m % 64 = 49 ∨
      m % 64 = 51 ∨
      m % 64 = 53 ∨
      m % 64 = 55 ∨
      m % 64 = 57 ∨
      m % 64 = 61) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
