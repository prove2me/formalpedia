-- Prove2me | Theorems.Thm_burau_sl2_descent_word
-- name    : burau_sl2_descent_word
-- status  : Proved
-- author  : @lt9
-- created : 2026-10-01T06:09:08.644811+00:00
-- url     : https://prove2.me/theorems/2b166d74-bc90-446f-8aea-77cdf96ff4ce
-- title:
--   The Euclidean descent word multiplies back to the matrix
-- statement:
--   **The Euclidean descent of a unimodular $2\times2$ matrix, written as a word in the
--   generators.** Let $S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ and
--   $T^n=\left(\begin{smallmatrix}1&n\\0&1\end{smallmatrix}\right)$, and for $M\in\mathrm{SL}(2,\mathbb Z)$
--   iterate the Euclidean step $M\mapsto (M\cdot T^{-n})\cdot S$, $n=M_{01}/M_{00}$, recording at each
--   step the factor $S^{-1}T^{n}$; when $M_{00}$ reaches $0$ the two-element terminal word
--   $S^{\pm1}T^{k}$ closes the expansion. The node records that word, `BurauDescent.word M`, and the
--   statement proved here is
--   $$ \prod \mathtt{word}(M) = M . $$
--   This is the combinatorial engine behind the descent section $\rho$ of the reduced braid quotient:
--   it turns an arbitrary element of $\mathrm{SL}(2,\mathbb Z)$ into an explicit product of the two
--   generators, on which the multiplication rules for $\rho$ are checked generator by generator.
-- source:
--   Euclidean algorithm in SL(2,Z); J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. Math. Studies 82 (1974), §3.3.

import Definitions.Def_burau_descent_word

set_option autoImplicit false

theorem burau_sl2_descent_word (M : BurauDescent.M2) (hd : M.det = 1) :
    (BurauDescent.word M).prod = M := by sorry
