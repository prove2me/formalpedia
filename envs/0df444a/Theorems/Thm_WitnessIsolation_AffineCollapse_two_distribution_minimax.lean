-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_two_distribution_minimax
-- name    : WitnessIsolation.AffineCollapse.two_distribution_minimax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:13.602161+00:00
-- url     : https://prove2.me/theorems/09fe6479-052d-45d6-b67a-037dbfee33d5
-- title:
--   Lemma 3.1 — Two-distribution minimax
-- statement:
--   Let Y,N be disjoint nonempty subsets of the ℓ-bit cube, let S be a gate budget, and let 0<ε≤1. Either there are arbitrary real distributions μ on Y and ν on N such that every circuit C of size at most S has acceptance gap at most ε, or a deterministic circuit separates all of Y from all of N. The separator obeys
--
--   $$|C|\le K M\bigl(S+\log_2(M+2)+1\bigr),\qquad M=\lceil32(\ell+2)\epsilon^{-2}\rceil.$$
--
--   One positive real K works for every length, budget, pair of sets and ε. No samplability or rationality is required of μ or ν. This dichotomy supplies the quantitative bridge from the absence of small separators to indistinguishable source laws.
--
--   Differences from the source:
--   - encoding: size O(M(S+log(M+2)+1)) → one existential positive real K preceding ℓ,S,Y,N,ε; reason: this is the uniform meaning of the source O bound in the fixed gate basis
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Lemma 3.1, printed p. 7, PDF p. 8, including Eq. (3.1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_probability

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Lemma 3.1, including the absolute gap and the uniform gate overhead. -/
theorem two_distribution_minimax :
    ∃ K : ℝ, 0 < K ∧ ∀ (ℓ S : ℕ) (Y N : Set (Bits ℓ)) (ε : ℝ),
      Y.Nonempty → N.Nonempty → Disjoint Y N → 0 < ε → ε ≤ 1 →
      (∃ μ ν : Law (Bits ℓ), μ.Supported Y ∧ ν.Supported N ∧
        Indistinguishable μ ν S ε) ∨
      (∃ C : Circuit ℓ 1, Separates C Y N ∧
        (C.size : ℝ) ≤ K * (Nat.ceil (32*((ℓ:ℝ)+2)*ε^(-2:ℤ)) : ℝ) *
          ((S:ℝ) + Real.logb 2 ((Nat.ceil (32*((ℓ:ℝ)+2)*ε^(-2:ℤ)) : ℝ)+2)+1)) := by sorry

end WitnessIsolation.AffineCollapse
