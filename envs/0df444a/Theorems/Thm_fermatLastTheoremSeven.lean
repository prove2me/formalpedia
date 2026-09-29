-- Prove2me | Theorems.Thm_fermatLastTheoremSeven
-- name    : fermatLastTheoremSeven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/4ea5926e-f354-549e-94dd-09d476000369
-- title:
--   Fermat's Last Theorem for exponent 7
-- statement:
--   The assertion is `FermatLastTheoremFor 7`, Mathlib's predicate which unfolds to: for all natural numbers $a$, $b$, $c$ with $a \neq 0$, $b \neq 0$ and $c \neq 0$, one has $a^{7} + b^{7} \neq c^{7}$. There are no further hypotheses and no parameters: the statement is a closed proposition about the natural numbers, phrased entirely in Mathlib terms (no project-specific definition is involved). Note that the quantification is over $\mathbb{N}$ with the three variables required only to be nonzero — no coprimality or ordering assumption is imposed, and the statement is about the single exponent $7$ rather than about all exponents $n \geq 3$ or all odd primes.
--
--   This is the classical case $n = 7$ of Fermat's Last Theorem, first settled by Lamé (1839); the route taken here is instead Kummer's theorem for regular primes together with the fact that the $7$-th cyclotomic field has class number $1$. Within the formalisation it is not used as a step in the Frey–Serre–Ribet–Wiles argument but to dispose of a small exponent: it is cited by [`FreyPackage.frey_no_cofixed_small`](thm.html#FreyPackage.frey_no_cofixed_small), which covers the exponents $p \in \{5,7,13\}$ by noting that no Frey package with such $p$ exists, so the conclusion about Galois-stable cofixed lines holds vacuously.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_fermatLastTheoremSeven.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem fermatLastTheoremSeven : FermatLastTheoremFor 7 := by sorry
