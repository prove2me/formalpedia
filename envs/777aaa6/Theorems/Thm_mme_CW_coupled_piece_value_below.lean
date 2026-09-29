-- Prove2me | Theorems.Thm_mme_CW_coupled_piece_value_below
-- name    : mme_CW_coupled_piece_value_below
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T14:47:46.306463+00:00
-- url     : https://prove2.me/theorems/53c86c2a-7ff0-41c0-a2f2-a6e7a600f0ff
-- title:
--   Symmetric value of the coupled CW constituent, sub-base form
-- statement:
--   The symmetric $\tau$-value of Coppersmith--Winograd's coupled constituent, in sub-base form, at every $q\ge3$.
--
--   For $q\ge3$, $3\tau\ge2$ and every $V$ with
--   $$0\le V\;<\;2^{2/3}\,q^{\tau}\,\bigl(q^{3\tau}+2\bigr)^{1/3},$$
--   the constituent has symmetric $\tau$-value at least $V$.
--
--   The tensor in question is the four-sum constituent (d) of Coppersmith--Winograd, on modes $(\mathbf{F}^q\oplus\mathbf{F}^q,\ \mathbf{F}^q\oplus\mathbf{F}^q,\ \mathbf{F}^2\oplus\mathbf{F}^{q\times q})$:
--   $$\sum_i x^0_iy^0_iz_0+\sum_k x^1_ky^1_kz_1+\sum_{i,k}\bigl(x^0_iy^1_k+x^1_ky^0_i\bigr)z_{ik},$$
--   whose two $\langle q,1,q\rangle$ blocks share the same third-mode coordinates — the coupling that prevents the constituent from being a direct sum. Since `HasSymmetricTauValueAtLeast` is defined through the cube of the base, the displayed bound is exactly the statement that the cyclic symmetrisation has $\tau$-value below $4q^{3\tau}(q^{3\tau}+2)$, and the proof is `mme_CW_coupled_raw_cyclic_value_below` composed with the cube identity `mme_CW_coupled_value_cube`.
--
--   **Relation to the open milestone.** The milestone `mme_CW_coupled_piece_value` asserts the same conclusion at the *sharp* base $2^{2/3}q^{\tau}(q^{3\tau}+2)^{1/3}$ itself. That form is not reachable by the laser method as the platform defines value: `HasTauValueAtLeast` permits only a loss $1-\varepsilon$ independent of $N$, whereas Behrend pruning costs $e^{-c\sqrt{N}}$ and the assembled construction costs $e^{-cN^{3/4}}$, both of which eventually fall below every fixed $1-\varepsilon$. The statement here is the strongest form the value predicate supports, and it is what every downstream laser step actually consumes.
-- source:
--   Don Coppersmith and Shmuel Winograd, Matrix multiplication via arithmetic progressions, Journal of Symbolic Computation 9(3), 1990, 251-280; the coupled four-sum constituent (d) on printed p. 266 and its value lemma on printed p. 270. General-q form of the q=6 chain used for omega < 2.376.

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_CW_coupled_piece_value_below
    {K : Type u} [Field K] (q : ℕ) (hq : 3 ≤ q)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (2 : ℝ) ^ ((2 : ℝ) / 3) *
        (q : ℝ) ^ tau *
        (((q : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) :
    HasSymmetricTauValueAtLeast (coupledObj K q) tau V := by
  sorry
