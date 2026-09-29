-- Prove2me | Theorems.Thm_MarkovChainCLT_alphaMixingCoef_antitone
-- name    : MarkovChainCLT.alphaMixingCoef_antitone
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T12:20:50.408219+00:00
-- url     : https://prove2.me/theorems/694da51a-1fbd-44ad-af53-f6f0d0b55e46
-- title:
--   The strong mixing coefficients $\alpha(n)$ are nonincreasing in the lag
-- statement:
--   **The strong mixing coefficients of a sequence are nonincreasing in the lag.**
--
--   Let $Y=(Y_n)_{n\ge0}$ be a sequence of random elements on a probability space $(\Omega,\mathcal F,P)$ and let
--
--   $$\alpha(n)=\sup_{k\ge 0}\ \sup\bigl\{\,|P(A\cap B)-P(A)P(B)| \;:\; A\in\sigma(Y_0,\dots,Y_k),\ B\in\sigma(Y_{k+n},Y_{k+n+1},\dots)\,\bigr\}$$
--
--   be its strong (α-) mixing coefficients.  Then $m\le n$ implies $\alpha(n)\le\alpha(m)$.
--
--   The reason is purely structural: increasing the lag shrinks the future σ-algebra, $\sigma(Y_i:i\ge k+n)\subseteq\sigma(Y_i:i\ge k+m)$, so every pair $(A,B)$ admissible at lag $n$ is admissible at lag $m$; the supremum at lag $n$ is therefore taken over a subfamily of the one at lag $m$.  Two side facts make the comparison of suprema legitimate: the defining family is nonempty (take $A=B=\varnothing$), and for a probability measure it is bounded above by $1$, so both suprema are honest least upper bounds rather than the junk value that `sSup` assigns to an unbounded set.
--
--   Monotonicity is the first of Bradley's basic properties of the mixing coefficients, and it is what allows summability of $\alpha$ to be converted into a decay *rate*: a nonincreasing summable sequence satisfies $n\,\alpha(n)\to0$, which is the form in which the mixing hypothesis enters Bernstein's big-block/small-block scheme.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, Section 1 (the mixing coefficients are nonincreasing functions of the lag). The coefficient itself is Definition 1 of G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.alphaMixingCoef_antitone {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) :
    Antitone (fun n => alphaMixingCoef P Y n) := by sorry
