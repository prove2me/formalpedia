-- Prove2me | Theorems.Thm_northcott_projMulHeight_numberField
-- name    : northcott_projMulHeight_numberField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/8ae15468-0445-54c5-aa17-47f44822b27d
-- title:
--   Northcott's theorem for projective space over a number field
-- statement:
--   Let $K$ be a field equipped with the structure of a number field, and let $\iota$ be a finite index type. Consider the projective space $\mathbb{P}(K^{\iota})$ of the $K$-vector space $\iota \to K$ of $\iota$-tuples, i.e. `Projectivization K (ι → K)`, and on it the multiplicative absolute Weil height `Projectivization.mulHeight`, the function $\mathbb{P}(K^{\iota}) \to \mathbb{R}$ obtained from the height of a representing tuple (independent of the representative, as the height is invariant under scaling by $K^{\times}$). The assertion is that this height function satisfies `Northcott`: for every real bound $B$, the set of points of $\mathbb{P}(K^{\iota})$ whose multiplicative height is at most $B$ is finite. No further hypotheses are imposed; in particular $\iota$ is an arbitrary finite type, so the projective space in question is $\mathbb{P}^{n-1}$ for $n$ the cardinality of $\iota$, the statement being vacuous when $\iota$ is empty since then the vector space is trivial and the projective space empty. The statement is for the projective height over a fixed number field; it makes no claim about points of bounded height with varying field of definition.
--
--   This is Northcott's finiteness theorem for the absolute multiplicative height on projective space over a number field, the finiteness input underlying descent arguments. It is used in the form of the Northcott property for the naive height on the modular curve, via [`ModularCurve.JZero.naiveHeight_northcott`](thm.html#ModularCurve.JZero.naiveHeight_northcott).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_northcott_projMulHeight_numberField.lean

import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.Order.Northcott

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem northcott_projMulHeight_numberField (K : Type) [Field K] [NumberField K] (ι : Type) [Finite ι] :
    Northcott (Projectivization.mulHeight : Projectivization K (ι → K) → ℝ) := by sorry
