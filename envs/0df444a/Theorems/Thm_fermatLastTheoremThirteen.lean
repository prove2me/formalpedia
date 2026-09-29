-- Prove2me | Theorems.Thm_fermatLastTheoremThirteen
-- name    : fermatLastTheoremThirteen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/dceac4f6-8d9f-5125-a0b1-c76ff055fd3b
-- title:
--   Fermat's Last Theorem for exponent 13
-- statement:
--   The theorem asserts `FermatLastTheoremFor 13`, the Mathlib predicate which, unfolded, says: for all natural numbers $a$, $b$, $c$ with $a \neq 0$, $b \neq 0$ and $c \neq 0$, one has $a^{13} + b^{13} \neq c^{13}$. There are no hypotheses and no variables: the statement is a closed assertion about the single exponent $13$, phrased entirely in Mathlib terms (the predicate is the instance of `FermatLastTheoremWith` over $\mathbb{N}$ with exponent $13$, i.e. nonvanishing of the Fermat form with all three variables nonzero; by the standard Mathlib transfer lemmas this is equivalent to the corresponding statements over $\mathbb{Z}$ or $\mathbb{Q}$, but only the natural-number form is asserted here). Nothing about Frey curves, modular forms or Galois representations enters; the result is obtained from the project's theorem [`flt_regular`](thm.html#flt_regular), which proves `FermatLastTheoremFor p` for an odd prime $p$ satisfying a class number condition, namely that $p$ is coprime to the (finite) cardinality of `ClassGroup (𝓞 (CyclotomicField p ℚ))`, the class number of the $p$-th cyclotomic field. For $p = 13$ this condition is verified in the strongest possible way, by showing that the class number equals $1$.
--
--   This is Kummer's theorem on regular prime exponents specialised to $p = 13$, $13$ being regular because $\mathbb{Q}(\zeta_{13})$ has class number one; the formal statement is the exponent-$13$ instance only, with no quantification over regular primes and no reference to Bernoulli numbers, the regularity input being supplied in the form of a class-number-one statement. Unlike the textbook formulation over $\mathbb{Z}$, the conclusion is stated for nonzero natural numbers. It is used in [`FreyPackage.frey_no_cofixed_small`](thm.html#FreyPackage.frey_no_cofixed_small), where the cases $p = 5, 7, 13$ of the exponent of a Frey package are excluded outright, so that the small-exponent cases of the main line of argument can be dispatched without the Frey-curve machinery.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_fermatLastTheoremThirteen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem fermatLastTheoremThirteen : FermatLastTheoremFor 13 := by sorry
