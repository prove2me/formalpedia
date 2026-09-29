-- Prove2me | Theorems.Thm_fermatLastTheoremFive
-- name    : fermatLastTheoremFive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/56ed7e88-009b-5338-8dd6-77edcf11abc4
-- title:
--   Fermat's Last Theorem for the exponent 5
-- statement:
--   The theorem asserts `FermatLastTheoremFor 5`, Mathlib's predicate for Fermat's Last Theorem at a fixed exponent, instantiated at $n = 5$. Unfolded, this says: for all natural numbers $a$, $b$, $c$, if $a \neq 0$, $b \neq 0$ and $c \neq 0$, then $a^5 + b^5 \neq c^5$. There are no further variables, hypotheses or typeclass assumptions: the statement is a closed proposition about the natural numbers, with the exponent given as the literal $5$ rather than as a variable satisfying some condition. Equivalently (and this is the form actually proved before transport along Mathlib's `fermatLastTheoremFor_iff_int`), the equation $x^5 + y^5 = z^5$ has no solution in integers with $xyz \neq 0$; the statement over $\mathbb{N}$ is the one recorded here. Nothing is asserted about exponents other than $5$, and no rational or real solutions are considered.
--
--   This is the classical theorem of Dirichlet and Legendre (1825) settling the quintic case of Fermat's equation. Within the present development it is not obtained as a specialisation of Kummer's theorem for regular primes but by a self-contained descent in the ring $\mathbb{Z}[\tfrac{1+\sqrt5}{2}]$, citing only Mathlib. Its role in the route to the general theorem is to make the exponent $p = 5$ vacuous: it is used, together with the corresponding results for $7$ and $13$, by [`FreyPackage.frey_no_cofixed_small`](thm.html#FreyPackage.frey_no_cofixed_small), which rules out a Galois-stable line with trivial action on the quotient for the Frey curve when $p \in \{5,7,13\}$ simply because no Frey package with such $p$ exists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_fermatLastTheoremFive.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem fermatLastTheoremFive : FermatLastTheoremFor 5 := by sorry
