-- Prove2me | Theorems.Thm_WinterExtrinsic_theorem_2
-- name    : WinterExtrinsic.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:20:20.635768+00:00
-- url     : https://prove2.me/theorems/b2fc747f-571f-41db-a9ec-48971106d5f2
-- title:
--   Theorem 2 — $a^{\otimes l}$ is a uniform mixture of $2^{l(H(\lambda)-I(\lambda;\hat\rho))+O(\sqrt l)}$ POVMs with $2^{lI(\lambda;\hat\rho)+O(\sqrt l)}$ outcomes
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^d$ and $a = (a_1, \dots, a_m)$ a POVM on $\mathbb C^d$. Write $\lambda_j = \mathrm{Tr}(\rho a_j)$ and $\hat\rho_j = \lambda_j^{-1}\sqrt\rho\, a_j\sqrt\rho$ for the canonical ensemble, $H(\lambda) = -\sum_j \lambda_j \log_2\lambda_j$ for the Shannon entropy of $\lambda$, and
--
--   $$I(\lambda;\hat\rho) = H(\rho) - \sum_j \lambda_j H(\hat\rho_j)$$
--
--   for its Holevo quantity (entropies in bits). Let $\epsilon > 0$.
--
--   Then there is a constant $C$ such that for every $l \in \mathbb N$ there exist an integer $N \ge 1$ and POVMs $A^{(1)}, \dots, A^{(N)}$ on $(\mathbb C^d)^{\otimes l}$ with outcome set $[m]^l$ such that:
--
--   1. $N \le 2^{\,l(H(\lambda) - I(\lambda;\hat\rho)) + C\sqrt l}$;
--   2. each $A^{(\nu)}$ is supported on at most $2^{\,l I(\lambda;\hat\rho) + C\sqrt l}$ words, i.e. $\#\{j^l : A^{(\nu)}_{j^l} \ne 0\} \le 2^{\,l I(\lambda;\hat\rho) + C\sqrt l}$;
--   3. the uniform mixture $A = \frac1N\sum_{\nu=1}^N A^{(\nu)}$ satisfies condition (CM):
--
--   $$\sum_{j^l \in [m]^l} \frac12 \Big\|\sqrt{\rho^{\otimes l}}\,\big(A_{j^l} - a_{j_1}\otimes\cdots\otimes a_{j_l}\big)\sqrt{\rho^{\otimes l}}\Big\|_1 \le \epsilon .$$
--
--   So, up to an error $\epsilon$ on the source $\rho^{\otimes l}$, performing $a^{\otimes l}$ amounts to choosing $\nu$ uniformly at random (about $l(H(\lambda) - I)$ bits of "extrinsic" data, independent of the state) and then performing $A^{(\nu)}$, which yields only about $lI(\lambda;\hat\rho)$ bits of "intrinsic" data. Theorem 8 of the paper shows these rates are optimal.
--
--   **Formalization Note** Logs and exps are to base 2 (`exp2 x = 2^x`; `shannon`, `vnEntropy` in bits). The $O(\sqrt l)$ terms are a single constant $C$, chosen after $\rho$, $a$, $\epsilon$ and before $l$. Words are `Fin l → Fin m`; operators on $(\mathbb C^d)^{\otimes l}$ are matrices indexed by `Fin l → Fin d`. $\rho$ need not be invertible, and $\hat\rho_j := 0$ when $\lambda_j = 0$ (it enters only with weight $\lambda_j$).
--
--   Differences from the source:
--   - reading: "$M = \exp(lI(\lambda;\hat\rho) + O(\sqrt l))$, $N = \exp(l(H(\lambda) - I(\lambda;\hat\rho)) + O(\sqrt l))$" → there is $C$, depending on $(\rho, a, \epsilon)$ and fixed before $l$, such that for every $l$ the supports are at most $2^{lI + C\sqrt l}$ and $N \le 2^{l(H(\lambda)-I) + C\sqrt l}$; reason: the standard Landau meaning with $l$ the only asymptotic variable; the paper states uniformity of constants explicitly where it means it (Theorems 6 and 8), not for Theorem 2; $M$ is a bound on support sizes, and only the upper bound on $N$ has content ($N$ can be inflated by repeating POVMs).
--   - reading: "condition (CM) is satisfied" → for every $\epsilon > 0$, quantified before $C$; reason: (CM) carries a parameter $\epsilon$, and the proof works for every $\epsilon > 0$ (it ends with $2\epsilon + \sqrt{2\epsilon} + \sqrt{6\epsilon}$ and rescales).
--   - reading: the state $\rho$ → any density matrix, not necessarily invertible; reason: Theorem 2 assumes no invertibility (only the proof of Theorem 6, p.7, does), and (CM), $\lambda$ and $\hat\rho$ depend on $\rho$ only through $\sqrt\rho\,a_j\sqrt\rho$ and $\rho^{\otimes l}$.
--   - encoding: $\mathcal H = \mathbb C^d$, outcomes $1..m$, words $j^l$, $\rho^{\otimes l}$, $\sqrt{\cdot}$, $\|\cdot\|_1$, exp and log → `Fin d`, `Fin m`, `Fin l → Fin m`, `wordTensor`, `cfc Real.sqrt`, unhalved `traceNorm` with an explicit $\frac12$, `exp2`/`logb 2`; $\hat\rho_j = 0$ when $\lambda_j = 0$; $l = 0$ included (there $N = 1$, $A^{(1)} = a^{\otimes 0}$ works); reason: Lean representation, same instances.
-- source:
--   Winter, "Extrinsic" and "intrinsic" data in quantum measurements, arXiv:quant-ph/0109050v3, §II, Theorem 2, p.3 (condition (CM), p.3; canonical ensemble, pp.3–4; logs and exps to base 2, p.2)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_WinterExtrinsic_holevoInfo
import Definitions.Def_WinterExtrinsic_supportCard
import Definitions.Def_WinterExtrinsic_cmError

namespace WinterExtrinsic

open QAlgorithms
open QAlgorithms.Papers.Independent.Renew46.P43 (exp2)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

/-- Theorem 2 (asymptotic convex decomposition of a POVM). Let `ρ` be a density matrix on `ℂ^d`,
`a` an `m`-outcome POVM and `ε > 0`, with canonical ensemble `λ_j = Tr(ρ a_j)`,
`ρ̂_j = √ρ a_j √ρ / λ_j` and `I(λ; ρ̂) = H(ρ) − Σ_j λ_j H(ρ̂_j)`. There is a constant `C` such that
for every `l` there are `N ≥ 1` with `N ≤ 2^{l(H(λ) − I(λ;ρ̂)) + C√l}` and POVMs
`A^{(1)}, …, A^{(N)}` on `[m]^l`, each with at most `2^{l I(λ;ρ̂) + C√l}` nonzero operators, whose
uniform mixture `A = (1/N) Σ_ν A^{(ν)}` satisfies (CM):
`Σ_{j^l} ½ ‖√(ρ^{⊗l})(A_{j^l} − a_{j^l})√(ρ^{⊗l})‖₁ ≤ ε`.

Winter, *"Extrinsic" and "intrinsic" data in quantum measurements*, arXiv:quant-ph/0109050v3,
§II, Theorem 2, p.3: "There exist POVMs A^{(ν)} on [m]^l, ν = 1, …, N, each supported on a set of
cardinality at most M, where M = exp(lI(λ;ρ̂) + O(√l)), N = exp(l(H(λ) − I(λ;ρ̂)) + O(√l)), such
that for A = 1/N Σ_ν A^{(ν)} condition (CM) is satisfied."

**Formalization Note.** Logs and exps are to base 2 (p.2): `exp2 x = 2^x`, entropies in bits
(`shannon`, `vnEntropy`). `O(√l)` is read as `C√l` with one constant `C` chosen after `ρ`, `a`,
`ε` and before `l`. `ρ` need not be invertible. Words `j^l` are `Fin l → Fin m`; operators on
`(ℂ^d)^{⊗l}` are matrices indexed by `Fin l → Fin d`. -/
theorem theorem_2 {d m : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : IsDensityMatrix ρ)
    (a : Fin m → Matrix (Fin d) (Fin d) ℂ) (ha : IsPOVM a) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ l : ℕ, ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ exp2 (l * (shannon (canonWeight ρ a) - holevoInfo ρ a) + C * Real.sqrt l) ∧
      ∃ A : Fin N → (Fin l → Fin m) → Matrix (Fin l → Fin d) (Fin l → Fin d) ℂ,
        (∀ ν, IsPOVM (A ν)) ∧
        (∀ ν, (supportCard (A ν) : ℝ) ≤ exp2 (l * holevoInfo ρ a + C * Real.sqrt l)) ∧
        cmError ρ a l (fun w => ((N : ℂ)⁻¹) • ∑ ν, A ν w) ≤ ε := by sorry

end WinterExtrinsic
