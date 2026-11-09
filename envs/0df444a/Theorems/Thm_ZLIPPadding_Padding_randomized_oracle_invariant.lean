-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_randomized_oracle_invariant
-- name    : ZLIPPadding.Padding.randomized_oracle_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:44.515535+00:00
-- url     : https://prove2.me/theorems/c8acedac-e88f-4c16-9f5c-e7c072a11377
-- title:
--   Corollary 2.6 — Randomizing a vector-search oracle
-- statement:
--   Let $G$ be a promised Gram matrix and let $\mu$ be an ideal jointly invariant law of a change of basis $(H,U)$. Fix a basis-independent set of valid coordinate answers, preserved by the Gram stabilizer, and a correct oracle on every Gram matrix equivalent to $G$. The oracle's private coins are independent of the randomizer and its law depends only on $H$. Then the returned coordinates $c=Uq$, interpreted geometrically as $Bc$, are valid and have an automorphism-invariant law $\nu$.
--
--   For every positive-probability orbit $\mathcal O$,
--   $$\Pr_\nu[c=z\mid c\in\mathcal O]=\frac1{|\mathcal O|}\qquad(z\in\mathcal O).$$
--   If all valid answers lie in one prescribed orbit, the output samples that orbit uniformly. Repeating the pair experiment with fresh independent randomizer and oracle coins gives independent samples, with joint law $\nu^{\otimes t}$ for every number $t$ of trials.
--
--   This transfers the input law's joint invariance to arbitrary correct vector-search oracles.
--
--   Differences from the source:
--   - generalization: the law produced by Lemma 2.5 → any supplied ideal joint-invariant law; reason: the Lemma 2.5 law satisfies exactly these hypotheses, and every clause specializes to the corollary
--   - encoding: geometric vectors Bz and Aut(L) → integer coordinates z and the Gram stabilizer; reason: B is invertible and transports these objects bijectively, for every real ambient rotation
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 9 (PDF p. 10), Corollary 2.6

import Definitions.Def_ZLIPPadding_Padding_Laws

open scoped ENNReal

namespace ZLIPPadding.Padding
/-- Corollary 2.6, printed p.9 / PDF p.10. Coordinates faithfully transport by B.
Generalization: any supplied ideal joint-invariant law, not only the named implementation. -/
theorem randomized_oracle_invariant
    (n : ℕ) (G : ZMat n) (hG : ValidGram G)
    (μ : PMF (ZMat n × ZMat n)) (hμ : IdealRandomization G μ)
    (Good : ZVec n → Prop)
    (hGood : ∀ V, Stabilizes G V → ∀ z, Good z → Good (V.mulVec z))
    (A : ZMat n → PMF (ZVec n))
    (hA : ∀ H U, Unimodular U → H = U.transpose * G * U →
      ∀ q, A H q ≠ 0 → Good (U.mulVec q)) :
    let ν := mappedLaw μ A
    (∀ z, ν z ≠ 0 → Good z) ∧
    (∀ V, Stabilizes G V → ν.map V.mulVec = ν) ∧
    (∀ a, mass ν (gramOrbit G a) ≠ 0 →
      (gramOrbit G a).Finite ∧ ∀ z ∈ gramOrbit G a,
        ν z / mass ν (gramOrbit G a) = 1 / ((gramOrbit G a).ncard : ℝ≥0∞)) ∧
    (∀ a, (∀ z, Good z → z ∈ gramOrbit G a) →
      (∀ z, ν z ≠ 0 → z ∈ gramOrbit G a) ∧
      ∀ z ∈ gramOrbit G a, ν z = 1 / ((gramOrbit G a).ncard : ℝ≥0∞)) ∧
    (∀ t : ℕ, repeatedMapped μ A t = iid ν t) := by sorry
end ZLIPPadding.Padding
