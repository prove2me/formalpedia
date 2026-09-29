-- Prove2me | Theorems.Thm_mme_borderRank_kronPow_le
-- name    : mme_borderRank_kronPow_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T19:22:40.181003+00:00
-- url     : https://prove2.me/theorems/1ee8a95a-ef25-42fa-8e7b-6e6b7c09124e
-- statement:
--   **Border rank is multiplicative under Kronecker powers.**
--
--   For any order-$d$ tensor object $X$ with border rank at most $r$ (i.e. $X$ degenerates from $I_r$), the $N$-fold Kronecker power $X^{\otimes N}$ has border rank at most $r^N$:
--
--   $$\underline R(X) \leq r \;\implies\; \underline R\bigl(X^{\otimes N}\bigr) \leq r^N.$$
--
--   Formally: `Degenerates X (diagObj K d r) → Degenerates (X.kronPow N) (diagObj K d (r^N))`.
--
--   **Proof outline.** Given a `PolyFamily Φ` witnessing the degeneration $X \leftarrow I_r$ (an order-$h$ polynomial deformation with $r$ rank-one terms approaching $X$), take the Kronecker product $\Phi^{\otimes N}$ (mode-wise tensor product of the $\Phi$ data) to obtain a new `PolyFamily` witnessing $X^{\otimes N} \leftarrow I_r^{\otimes N} \cong I_{r^N}$ (using $(\mathrm{diagObj}\,r)^{\otimes N} = \mathrm{diagObj}\,(r^N)$ up to canonical isomorphism). The order of the resulting degeneration is $N \cdot h$.
--
--   **Reusability — abstract Layer-2 bridge.** Combined with the platform's already-PROVED `mme_degenerates_asymptoticRank_le`, this discharges the asymptotic-rank scaling step in L1-α's chain:
--
--   $$\underline R(T) \leq R \;\implies\; \underline R(T^{\otimes N}) \leq R^N \;\implies\; \widetilde R(T^{\otimes N}) \leq R^N$$
--
--   for every tensor $T$.
--
--   **Why this is the right lemma for L1-α's chain.** The previously-uploaded `mme_tensorAsymptoticRank_kronPow_le` has a direction issue (the stated $\leq$ direction requires Fekete's subadditive lemma; the trivial direction is $\geq$). The border-rank route here avoids that: border rank is genuinely submultiplicative by the explicit `PolyFamily` Kronecker construction, no asymptotic limit needed.
--
--   **Universal reuse.** Every future ω-bound improvement (Stothers, Vassilevska Williams, Le Gall, Alman–VW, …) needs the analog "border rank bounds get carried through Kronecker powers". This abstract leaf is the canonical reusable form.
-- source:
--   https://arxiv.org/abs/2212.11824

import Definitions.Def_mme_degeneration
open MME
universe u

theorem mme_borderRank_kronPow_le {K : Type u} [Field K] {d : ℕ} (X : TensorObj K d) (N r : ℕ) (_h : Degenerates X (TensorObj.diagObj K d r)) : Degenerates (X.kronPow N) (TensorObj.diagObj K d (r ^ N)) := by sorry
