-- Prove2me | Theorems.Thm_BookSixth_bump_perturbation_lipschitz_v3
-- name    : BookSixth.bump_perturbation_lipschitz_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T01:58:18.421314+00:00
-- url     : https://prove2.me/theorems/75689270-e72e-482b-84e9-09a60a3a3a0e
-- title:
--   A finite sum of cut-off-scaled displacements is Lipschitz with per-index constant M + (K+1)L, for any common Lipschitz constant K on the similarities
-- statement:
--   Let $\chi_i : \mathrm{Space3} \to \mathbb{R}$ be $1$-Lipschitz maps bounded in absolute value by $L$, and let $S_i : \mathrm{Space3} \to \mathrm{Space3}$ be maps that are $(K)$-Lipschitz for a common $K \ge 1$, in the Mathlib sense `LipschitzWith (Real.toNNReal K)`, as already used by the Proved theorem `BookSixth.lipschitz_cutoff_infred` and satisfy $\|S_i y - y\| \le M$. Then the displacement field
--   $$
--     E(x) = \sum_{i} \chi_i(x) \bullet (S_i(x) - x)
--   $$
--   is Lipschitz with constant $\sum_i \bigl(M + (K+1)L\bigr)$:
--   $$
--     \|E(x) - E(y)\| \le \Bigl(\sum_{i}\bigl(M + (K+1)L\bigr)\Bigr)\,\|x - y\|.
--   $$
--
--   The point of the statement is the factor $K$ in place of the $1$ that appears in the Proved theorem `BookSixth.bump_perturbation_lipschitz_v2`, whose constant is $\sum_i (2L + M) = \sum_i (M + (1+1)L)$. The generalisation is what makes a *rotation* admissible: in the supremum norm on $\mathrm{Space3} = \mathrm{Fin}\,3 \to \mathbb{R}$ a rotation by angle $\theta$ is $1/\cos\theta$-Lipschitz, which exceeds $1$ for every non-trivial angle and tends to $1$ as $\theta \to 0$. Any version of the criterion with the hypothesis `LipschitzWith 1 (S i)` therefore cannot be applied to a non-trivial rotation, however small the rotation angle, and so cannot produce the local ambient homeomorphism that must act as a similarity on each moving round circle.
-- source:
--   The proof is the accepted proof of `BookSixth.bump_perturbation_lipschitz_v2` (target `00c3e7a7-f202-4293-aafe-919f3115ddd3`) with the constant generalised from $2$ to $1 + K$.
--
--   For $d_i z = S_i z - z$ and $c_i = \chi_i$ the key identity, valid in any module, is
--
--   ```
--   c x • d x - c y • d y = (c x - c y) • d x + c y • (d x - d y).
--   ```
--
--   The first product is controlled by the $1$-Lipschitzness of $\chi_i$ together with $\|S_i x - x\| \le M$, giving $M \|x - y\|$. The second is controlled by $\|\chi_i y\| \le L$ together with
--
--   ```
--   d x - d y = (S_i x - S_i y) - (x - y),
--   ```
--
--   whose norm is at most $(K + 1)\|x - y\|$ because $S_i$ is $K$-Lipschitz. The per-index constant is therefore $M + (K + 1) L$. Substituting $K = 1$ recovers $M + 2L$, exactly the constant of the Proved `bump_perturbation_lipschitz_v2`, which is the consistency check on the generalisation.
--
--   Note that the sharper constant $M + L$ is **false**; see the sibling target `BookSixth.bump_perturbation_lipschitz` (`010c4541`), where an explicit counterexample with $n = 1$, $L = 3$, $M = 1$ gives left side $5$ against right side $4$. The reason is that the estimate $M$ applies to the factor $S_i x - x$, which is the *outer* vector, whereas the factor carrying the $L$ bound is the *scalar* $\chi_i y$.
--
--   Note that `LipschitzWith` takes its constant in `NNReal`, so the hypothesis is written `LipschitzWith (Real.toNNReal K)`; this matches the Proved `BookSixth.lipschitz_cutoff_infred` (9e16de8e), which is stated with `LipschitzWith (Real.toNNReal (1 / d))`. The coercion is harmless because `hK : 1 ≤ K` gives `0 ≤ (Real.toNNReal K : ℝ)`.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bump_perturbation_lipschitz_v3 (n : ℕ) (K L M : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 1 ≤ K)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (hchi : ∀ i, LipschitzWith 1 (chi i))
    (hchiL : ∀ i x, ‖chi i x‖ ≤ L)
    (hS : ∀ i, LipschitzWith (Real.toNNReal K) (S i))
    (hSiy : ∀ i y, ‖S i y - y‖ ≤ M) :
    ∀ x y : Space3,
      ‖(∑ i, chi i x • (S i x - x)) - ∑ i, chi i y • (S i y - y)‖
        ≤ (∑ i : Fin n, (M + (K + 1) * L)) * ‖x - y‖ := by sorry
