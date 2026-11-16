-- Prove2me | Theorems.Thm_ZeroExtensionGap_Supplement_theorem_2_np_hardness
-- name    : ZeroExtensionGap.Supplement.theorem_2_np_hardness
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:24:14.699859+00:00
-- url     : https://prove2.me/theorems/d393ca5c-3a67-4630-a7ec-9cc4e8cd0beb
-- title:
--   Theorem 2 — 0-Extension with exactly $k$ terminals is NP-hard to approximate within $c_\varepsilon\log^{1-\varepsilon}k$
-- statement:
--   For every $\varepsilon\in(0,1)$ there is a constant $c_\varepsilon>0$ such that, for arbitrarily large fixed integers $k\ge1$, it is NP-hard to approximate 0-Extension on instances with exactly $k$ terminals within the factor $c_\varepsilon\log^{1-\varepsilon}k$. In symbols:
--
--   $$\forall\varepsilon\in(0,1)\ \exists c_\varepsilon>0\ \forall K\ \exists k\ge\max(K,1):\quad \mathrm{Gap\text{-}0\text{-}Ext}\big(k,\ c_\varepsilon(\log k)^{1-\varepsilon}\big)\ \text{is NP-hard.}$$
--
--   Here $\log$ is the natural logarithm, and "$\mathrm{Gap\text{-}0\text{-}Ext}(k,\alpha)$ is NP-hard" means: for every language $L$ in NP over a finite nonempty alphabet there is a map $f$ from strings to codes of 0-Extension inputs, computable in polynomial time (on the binary string of the code), such that every $x\in L$ goes to a valid instance with exactly $k$ terminals and $\mathrm{OPT}\le\tau$, and every $x\notin L$ to a valid instance with exactly $k$ terminals and $\mathrm{OPT}>\alpha\tau$. The constant $c_\varepsilon$ is chosen before $k$; the reduction may depend on $k$.
--
--   The theorem says that the $O(\log k/\log\log k)$ approximation ratio of Fakcharoenphol, Harrelson, Rao and Talwar is optimal up to the exponent of $\log k$, unconditionally. The paper derives it from Theorem 1, the reduction of Manokaran, Naor, Raghavendra and Schwartz, and the Unique Games Theorem.
--
--   **Formalization Note.** NP and polynomial-time computability are Cook's Turing-machine notions (`CookPvsNP_defs`), and gap NP-hardness is the published `OptInapprox.MaxCut.GapNPHard`. The problem and $\mathrm{OPT}$ are the base mission's `ZeroExtensionGap.Instance`, applied to the instance of the code.
--
--   Differences from the source:
--   - encoding: instances with real nonnegative weights and a real metric, input format unspecified → codes with rational weights and rational metric values, written as binary strings (unary vertex count, binary numbers); reason: a complexity statement is about finite inputs, and rational data in binary is the standard bit model; every rational instance has a code.
--   - reading: "NP-hard to approximate within α" → gap NP-hardness of Yes = (valid, k terminals, OPT ≤ τ) versus No = (valid, k terminals, OPT > α·τ) under Cook's NP and polynomial-time many-one maps; reason: the page names no machine model or notion of hardness of approximation; this is the standard notion, the one the [MNRS08] reduction delivers, and an α-approximation algorithm separates the two sets.
--   - encoding: graph with possible parallel edges and loops → simple graph with merged (summed) weights and loops dropped; reason: neither changes the cost of any retraction.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Theorem 2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_ZeroExtensionGap_Supplement_GapYes
import Definitions.Def_OptInapprox_MaxCut_UGC

set_option autoImplicit false

namespace ZeroExtensionGap.Supplement

/-- Chen, Zhu, *Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission
(manuscript sha256 0cdea87b…), Theorem 2, p.3 (PDF p.5): for every `ε ∈ (0,1)` there is `c_ε > 0`
such that, for arbitrarily large fixed `k ≥ 1`, it is NP-hard to approximate 0-Extension on
instances with exactly `k` terminals within `c_ε log^{1−ε} k`.
**Formalization Note.** `c` is chosen before `k`, and "arbitrarily large fixed `k`" is
`∀ K, ∃ k ≥ K`; the reduction may depend on `k`. "NP-hard to approximate within `α`" is gap
NP-hardness (the published `OptInapprox.MaxCut.GapNPHard` over Cook's `NP` and polynomial-time
computable maps): every NP language over every finite nonempty alphabet reduces in polynomial time
to coded instances, members to `GapYes k` (valid, `k` terminals, `OPT ≤ τ`) and non-members to
`GapNo k α` (valid, `k` terminals, `OPT > α τ`). The claim is unconditional, as on the page.
Logarithms are natural (§2, p.5). -/
theorem theorem_2_np_hardness :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ 1 ≤ k ∧
      OptInapprox.MaxCut.GapNPHard Code.encode (GapYes k)
        (GapNo k (c * Real.log (k : ℝ) ^ (1 - ε))) := by sorry

end ZeroExtensionGap.Supplement
