-- Prove2me | Theorems.Thm_ZeroExtensionGap_theorem_1_earthmover_gap
-- name    : ZeroExtensionGap.theorem_1_earthmover_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:01:14.737527+00:00
-- url     : https://prove2.me/theorems/97fc9622-b66d-40ff-9cc1-58eaa1be07bf
-- title:
--   Theorem 1 — the earthmover relaxation has integrality gap at least $c_\varepsilon\log^{1-\varepsilon}k$
-- statement:
--   For every constant $\varepsilon\in(0,1)$ there is a constant $c_\varepsilon>0$ such that, for arbitrarily large $k$, there is a 0-Extension instance $I$ with $k$ terminals whose integrality gap for the earthmover relaxation satisfies
--
--   $$\frac{\mathrm{OPT}(I)}{\mathrm{EM}(I)}\ge c_\varepsilon(\log k)^{1-\varepsilon}.$$
--
--   Logarithms are natural. This nearly meets the $O(\log k/\log\log k)$ upper bound of Fakcharoenphol, Harrelson, Rao and Talwar, in the exponent of $\log k$, and improves the $\Omega(\sqrt{\log k})$ gap of Karloff, Khot, Mehta and Rabani.
--
--   Differences from the source:
--   - encoding: integrality gap (the word is not defined; p.32 computes $\mathrm{OPT}/\mathrm{EM}$) → `0 < I.EM` and `c * log k ^ (1 - ε) ≤ I.OPT / I.EM`; reason: the printed ratio presupposes $\mathrm{EM}>0$, and the hypothesis excludes only the undefined case
--   - encoding: for arbitrarily large $k$ → `∀ K, ∃ k, K ≤ k ∧ …`; reason: the usual meaning; p.32 obtains $k=n^t$ for large even $n$
--   - encoding: an undirected graph, possibly with parallel edges and loops, on a vertex set $V$ → a `SimpleGraph (Fin m)`; reason: merging parallel edges and dropping loops changes neither $\mathrm{OPT}$ nor $\mathrm{EM}$, and every finite vertex set is a copy of `Fin m`
--   - encoding: the minima $\mathrm{OPT}$, $W_D$, $\mathrm{EM}$ → `sInf` on the corresponding sets; reason: on an instance with nonempty $T$ the sets are nonempty and the minima are attained
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Theorem 1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_ZeroExtensionGap_Instance

namespace ZeroExtensionGap

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), Theorem 1, p.2 (PDF p.4).
**Formalization Note.** `c` is chosen before `k` ("for arbitrarily large `k`" is `∀ K, ∃ k ≥ K`), the instance is
valid (nonnegative weights, `D` a metric on `T`) and has exactly `k` terminals, and the integrality gap is the ratio
`OPT I / EM I`, computed on p.32 (PDF p.34). `0 < EM I` excludes only the case in which the printed ratio is undefined.
Logarithms are natural (§2, p.5). The vertex set is `Fin m`, which loses nothing for a finite vertex set. -/
theorem theorem_1_earthmover_gap :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      ∃ (m : ℕ) (I : Instance (Fin m)), I.IsValid ∧ I.T.card = k ∧ 0 < I.EM ∧
        c * Real.log (k : ℝ) ^ (1 - ε) ≤ I.OPT / I.EM := by sorry

end ZeroExtensionGap
