-- Prove2me | Definitions.Def_mme_subrank_capacity_poly
-- name    : mme_subrank_capacity_poly
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-31T19:28:30.441591+00:00
-- url     : https://prove2.me/theorems/11abc130-5894-48fa-a710-65baae741044
-- statement:
--   **Polynomial-witness subrank capacity** — the corrected refinement of `subrankCapacity` enforcing subexponential witness summand counts.
--
--   For `T : TensorObj K 3`, the polynomial-witness subrank capacity is
--
--   $$\widetilde V_{\mathrm{poly}}(T) \;:=\; \sup\Bigl\{ V \geq 1 \;\Bigm|\; \exists c,\;\forall \varepsilon > 0,\; \exists^{\infty} N,\; \exists\; \bigoplus_i \langle a_i,b_i,c_i\rangle \;\leq\; T^{\otimes N},\; k \leq (N{+}1)^c,\; V^N(1{-}\varepsilon) \leq \sum_i (a_ib_ic_i)^{1/3} \Bigr\}.$$
--
--   **Why the polynomial constraint matters.** The original `subrankCapacity` (uploaded earlier) lacks the subexponential bound on the witness summand count $k_N$. Without it, the canonical Hölder + asymptotic-limit argument used to derive $\omega \leq \log R / \log V$ fails: the factor $k_N^{(\omega-1)/N}$ does not converge to $1$ when $k_N$ is exponential in $N$. With the polynomial bound, $k_N^{1/N} \to 1$ and the canonical bridge `mme_omega_le_of_subrank_capacity_poly` becomes provable.
--
--   **Practical equivalence to the original.** Every realistic ω-bound construction (Strassen 1986, Coppersmith–Winograd 1990, Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, Alman–Vassilevska Williams 2020) produces a polynomial $k_N$ (typically a multinomial / Stirling count from the laser-method construction). So the poly version is the *natural* one for the asymptotic-spectrum bridge.
--
--   **Reusability.** Same abstract paper-agnostic role as the original; pairs with `mme_omega_le_of_subrank_capacity_poly`.
-- source:
--   https://arxiv.org/abs/2212.11824

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_mme_tensor_rank

/-! # Subrank capacity (polynomial-witness version)

A **refinement** of `subrankCapacity` (from `Def_mme_subrank_capacity`) that
adds the subexponential constraint on the witness summand count `k_N`.

The original `subrankCapacity` allows `k_N` exponential in `N` (only
implicitly bounded by `dim(T)^N`), which leaves the `Hölder + asymptotic
limit` argument too weak — the constant factor `k_N^{(ω-1)/N}` survives in
the limit. This refined version requires `k_N ≤ (N+1)^c` for some
polynomial degree `c`, making the limit argument work and giving the clean
abstract bridge `ω ≤ log R / log V` in
`mme_omega_le_of_subrank_capacity_poly`.

Every realistic ω-bound construction (Strassen 1986, Coppersmith–Winograd
1990, Stothers 2010, Vassilevska Williams 2012, Le Gall 2014,
Alman–Vassilevska Williams 2020) produces a polynomial `k_N` (typically a
multinomial / Stirling count); the laser method explicitly produces such
witnesses. So this refined form is the natural one for the asymptotic-
spectrum bridge. -/

universe u

open BigOperators Filter

namespace MME

variable {K : Type u} [Field K]

/-- **Polynomial-witness subrank capacity.** Like `subrankCapacity`, but
additionally requires the witness summand count to be polynomial in `N`. -/
noncomputable def subrankCapacityPoly (T : TensorObj K 3) : ℝ :=
  sSup { V : ℝ | 1 ≤ V ∧ ∃ c : ℝ,
    ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in atTop,
      ∃ (k : ℕ) (a b c' : Fin k → ℕ),
        (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
          (T.kronPow N)
        ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) }

end MME


