-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_orbit_label_recovery
-- name    : ZLIPPadding.Padding.Supplement.orbit_label_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:24:44.448858+00:00
-- url     : https://prove2.me/theorems/21ac4460-e4ef-481d-8835-881dec19fee9
-- title:
--   Theorem 4.1 — Statistical recovery of the complete orbit label
-- statement:
--   Let $n\ge2$, integer $m\ge1$, $L\cong\mathbb Z^n$, and suppose the nonempty uniform shell has $|\kappa|\ge\kappa_0>0$. For a prescribed $x=\sum_i a_iv_i\in S_m(L)$ and every $0<\eta<1$, a uniform executable algorithm returns the multiset $\{a_1^2,\ldots,a_n^2\}$ with probability at least $1-\eta$. It uses two independent batches of positive integer sizes satisfying
--
--   $$N_4\ge\max\!\left\{2,\frac{1024m^{10}}{c_n^2\kappa_0^4}\log\frac4\eta\right\},\qquad N_x\ge\frac{512m^6}{\kappa_0^2}\log\frac{4n}{\eta},\quad c_n=\frac{n(n-1)}{n+2}.$$
--
--   The sign is determined by exact shell counting with $O(nm^{3/2})$ integer operations. Remaining computation is polynomial in $n,m,\kappa_0^{-1},\log(1/\eta)$ and input and sample representation lengths. The numerical contract uses all ordered eigenvalues to error at most $1/8$, with multiplicities and zeros, and reports failure at zero estimated contrast. The hidden basis and true label are never inputs. This is a companion theorem to the padding goal.
--
--   Differences from the source:
--   - encoding: a randomized algorithm consuming two independent batches → a deterministic finite program on the two supplied batches, then its law under independent iid batches; reason: all randomness is in the oracle samples; exact rational encoding and spectral rounding recover the identical multiset
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 16 (PDF p. 17), Theorem 4.1

import Definitions.Def_ZLIPPadding_Padding_Supplement_Reductions

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem orbit_label_recovery :
    ∃ (P : Program) (c d C : ℕ), LabelProgram P c d ∧ 0 < C ∧
      (∀ n m, 2 ≤ n → 1 ≤ m →
        ((countLog n m).operations : ℝ) ≤ (C : ℝ)*n*m*Real.sqrt m) ∧
      ∀ (n m : ℕ) (μ : PMF (ZVec n)) (kap0 : ℝ), 2 ≤ n → 1 ≤ m →
        UniformOn μ (shell n m) → 0 < kap0 → kap0 ≤ |shellKappa n m| →
        LabelGuarantee P c d false n m μ kap0 := by sorry

end ZLIPPadding.Padding.Supplement
