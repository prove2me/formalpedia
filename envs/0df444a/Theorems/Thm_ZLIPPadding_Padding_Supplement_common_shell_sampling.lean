-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_common_shell_sampling
-- name    : ZLIPPadding.Padding.Supplement.common_shell_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:25:12.845326+00:00
-- url     : https://prove2.me/theorems/40641053-8443-47d1-b39a-079cb85d1197
-- title:
--   Theorem 5.1 — Sampling a common shell with an exact conditional law
-- statement:
--   Let the independent increments have a common nonzero, automorphism-invariant lattice law with norm at most $\gamma$. Supply positive integers $K,M$ with $K\gamma^2\le M/4$ and a valid $0\le\Delta\le1/32$. Write $p_K$ for the hidden-coordinate endpoint law and $H_K=\{1\le m\le M:w_m\ge1/(8M)\}$. Assume the explicit finite estimate: for every $m\in H_K$ there is $a_m>0$ such that $p_K(z)=a_m e^{e_z}$ with $|e_z|\le\Delta$ for every standard-shell vector $z$. For $N\ge1$ and $0<\beta<1/4$, put
--
--   $$T=\left\lceil\max\{128M^2\log(2M/\beta),8MN\}\right\rceil.$$
--
--   The specified bucket algorithm uses exactly $KT$ increment calls. It returns failure or a label $m\in[1,M]$ and $N$ vectors on $S_m(L)$, and returns a heavy label with probability at least $1-\beta$. Conditional on every returned label of positive probability, its vectors have exactly the product law $\mu_m^{\otimes N}$, where $\mu_m=\mathcal L(Y_K\mid\|Y_K\|^2=m)$ is automorphism invariant. For every heavy $m$ and every $x\in S_m(L)$,
--
--   $$\frac{e^{-2\Delta}}{|S_m(L)|}\le\mu_m(x)\le\frac{e^{2\Delta}}{|S_m(L)|}.$$
--
--   Time is polynomial in $K,M,N,\log(1/\beta)$, input length, oracle time and output length. No local central limit theorem or unconditional guarantee for arbitrary approximate-SVP oracles is assumed. This companion theorem is separate from the padding proof.
--
--   Differences from the source:
--   - encoding: the real failure budget beta and total running time including the oracle → the derived integer T is supplied as a finite budget; kernel execution counts KT requests and charges any per-call time bound; reason: no real number or proof witness is an executable input; T is exactly (5.4) and oracle costs are included
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 22 (PDF p. 23), Theorem 5.1

import Definitions.Def_ZLIPPadding_Padding_Supplement_Walk

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem common_shell_sampling :
    ∃ (P : Program) (c d : ℕ), 0 < c ∧
    ∀ (n K M N : ℕ) (B : QMat n) O U (π ν : PMF (ZVec n))
      (gamma Delta beta : ℝ) (R : ℕ),
      0 < n → 0 < K → 0 < M → 1 ≤ N → CoordLaw B O U π ν →
      SignedInvariant π →
      (∀ z, π z ≠ 0 → z ≠ 0 ∧ normSq z ≤ gamma^2) →
      0 ≤ gamma → (K : ℝ)*gamma^2 ≤ M/4 → LocalEstimate π K M Delta →
      0 < beta → beta < 1/4 →
      (∀ z, ν z ≠ 0 → (encVec z).length ≤ R) →
      let T := walkTrials M N beta
      let law := bucketLaw (basisGram B) ν K M N T
      let runs := walkRun P c d B ν K M N T (errorBits beta) R
      (∀ s, runs s ≠ 0 →
        Budget (powerBound c d (K+M+N+errorBits beta+(encBasis B).length+R)) s ∧
        s.queries.length = K*T ∧ (∀ w ∈ s.queries, w = encBasis B)) ∧
      runs.map (fun s => decodeWalk n s.core.output) = law ∧
      (∀ m zs, law (some (m,zs)) ≠ 0 →
        1 ≤ m ∧ m ≤ M ∧ zs.length = N ∧
          ∀ z ∈ zs, qnorm (basisGram B) z = m) ∧
      prob law {o | ∃ m zs, o = some (m,zs) ∧ m ∈ heavy π K M} ≥ 1-beta ∧
      (∀ m, mass law {o | ∃ zs, o = some (m,zs)} ≠ 0 →
        let cond := conditionalShell ν (basisGram B) K m
        ShellLaw m (cond.map U.mulVec) ∧ SignedInvariant (cond.map U.mulVec) ∧
        ∀ zs, law (some (m,zs)) =
          mass law {o | ∃ xs, o = some (m,xs)} * iid cond N zs) ∧
      (∀ m ∈ heavy π K M, ∀ z ∈ shell n m,
        let cond := conditionalShell π (1 : ZMat n) K m
        Real.exp (-2*Delta)/(shell n m).card ≤ (cond z).toReal ∧
          (cond z).toReal ≤ Real.exp (2*Delta)/(shell n m).card) ∧
      (∀ tau : ℕ, ∀ s, runs s ≠ 0 →
        s.core.bitCost + s.core.randomBits + s.core.peakCells + s.queries.length*tau ≤
          powerBound c d (K+M+N+errorBits beta+(encBasis B).length+R+tau)) := by sorry

end ZLIPPadding.Padding.Supplement
