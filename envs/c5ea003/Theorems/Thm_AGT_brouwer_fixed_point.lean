-- Prove2me | Theorems.Thm_AGT_brouwer_fixed_point
-- name    : AGT.brouwer_fixed_point
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:14:48.347067+00:00
-- url     : https://prove2.me/theorems/f5f0bc7e-d860-49ac-bc3b-39215b98cf44
-- title:
--   Brouwer fixed-point theorem
-- statement:
--   Every continuous self-map of a nonempty, compact, convex subset of a finite-dimensional real normed vector space has a fixed point:
--   $$K \subseteq E \text{ nonempty compact convex},\quad f : K \to K \text{ continuous} \implies \exists\, x \in K,\ f(x) = x.$$
--   This is **Brouwer's fixed-point theorem**, the engine behind Nash's existence theorem: *Algorithmic Game Theory* invokes it without proof for Theorem 1.8, and Mathlib currently has no form of it, so it enters the mission as an explicit milestone in reusable generality rather than as an assumed library fact.
--
--   *A note on the hypotheses.* Nonemptiness is essential ($\varnothing$ is compact and convex, and the empty self-map has no fixed point); continuity is required only on $K$, and the values of $f$ outside $K$ are irrelevant. Any proof route — Sperner's lemma, homology, analytic arguments — is acceptable; the statement fixes none.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, supporting classical result for Ch. 1, Theorem 1.8 (invoked without proof)

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace AGT

/-- **Brouwer fixed-point theorem** (supporting result for Theorem 1.8 of
*Algorithmic Game Theory*; the book invokes it without proof for Nash's
theorem).  Every continuous self-map of a nonempty compact convex subset of a
finite-dimensional real normed space has a fixed point.

The nonemptiness hypothesis is essential: the empty set is compact and
convex, and the (empty) self-map of it has no fixed point.  Mathlib currently
has no form of this theorem, which is precisely why it is worth having as a
milestone. -/
theorem brouwer_fixed_point {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  sorry

end AGT
