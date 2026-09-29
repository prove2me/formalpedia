-- Prove2me | Theorems.Thm_mme_dwz_q6_112_table2_primary_hash_family_rate
-- name    : mme_dwz_q6_112_table2_primary_hash_family_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:24:53.008113+00:00
-- url     : https://prove2.me/theorems/8fecd01a-536c-42b2-b304-abbacd555d53
-- title:
--   Exact Table-2 b-split primary hash families at the Appendix-A rate
-- statement:
--   Use the exact Section 6.3/Table 2 split parameter $b=21015/10^8$ for the $q=6$ component $(1,1,2)$. At source power $m=10^8t$, set $N=m/2$, $L=bm$, and $G=(1-2b)m/2$. There is a constant $C\ge0$ such that, for all sufficiently large $t$, a genuine primary hash family exists with $A$ outer shared-$Z$ fibers of common size $H$. Write $Z=\binom{2N}{L}\binom{2N-L}{L}$, $X=\binom{N}{G}$, $B=\binom{2G}{G}$, and $\eta=\exp(-C\sqrt{N+1})$. Its finite capacities satisfy $H\le4^N$, $Z\eta\le A$, $B\eta\le4X^2H$, and\n\n$$\n\frac{Z^3B^2}{16X^4}\eta^5\le A^3H^2.\n$$\n\nThe left side is the Appendix-A $(1,1,2)$ multinomial count up to the fixed factor $1/16$ and an explicit subexponential loss. This supplies the exact Table-2 combinatorial family consumed by the already formalized cyclic tensor-value certificate.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 and Table 2 (b=0.00021015), and Appendix A, proof of Lemma 4.6(d), PDF pp. 59-60 and 82-83; https://arxiv.org/abs/2210.10173.

import Mathlib
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss

open MME Filter Topology

theorem mme_dwz_q6_112_table2_primary_hash_family_rate :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t : ℕ in atTop,
        let N : ℕ := 50000000 * t
        let L : ℕ := 21015 * t
        let G : ℕ := 49978985 * t
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let loss : ℝ :=
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ)))
        ∃ A H : ℕ,
          ∃ _family : CWQ6PrimaryHashFamily N L G A H,
            H ≤ 4 ^ N ∧
            (Zcount : ℝ) * loss ≤ (A : ℝ) ∧
            (middle : ℝ) * loss ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
            ((((Zcount : ℝ) ^ 3 * (middle : ℝ) ^ 2) /
                  (16 * (Xcount : ℝ) ^ 4)) * loss ^ 5) ≤
              (A : ℝ) ^ 3 * (H : ℝ) ^ 2 := by
  sorry
