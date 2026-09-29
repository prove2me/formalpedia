-- Prove2me | Theorems.Thm_ABC_explicit_bound
-- name    : ABC.explicit_bound
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:54:45.463413+00:00
-- url     : https://prove2.me/theorems/0300ef37-f1e7-43e4-984d-17d28ac2675f
-- title:
--   Explicit form of the $abc$ conjecture: $c \le \kappa(\varepsilon)\,\operatorname{rad}(abc)^{1+\varepsilon}$
-- statement:
--   This is the **explicit (bounded) form of the $abc$ conjecture** of Oesterle and Masser.
--
--   For a natural number $n$ write $\operatorname{rad}(n)$ for the radical of $n$, the product of the distinct primes dividing $n$. Call a triple $(a,b,c)$ of positive integers an *$abc$-triple* when $a+b=c$ and $a$, $b$, $c$ are pairwise coprime. The assertion is:
--
--   $$\text{for every } \varepsilon>0 \text{ there is a constant } \kappa(\varepsilon)>0 \text{ such that } c \;\le\; \kappa(\varepsilon)\,\operatorname{rad}(abc)^{1+\varepsilon} \text{ for every } abc\text{-triple } (a,b,c).$$
--
--   Here $\varepsilon$ is an arbitrary positive real, the constant $\kappa(\varepsilon)$ is allowed to depend on $\varepsilon$ but on nothing else, and the exponent $1+\varepsilon$ is a real exponent, so $\operatorname{rad}(abc)^{1+\varepsilon}$ is a real power. The inequality says that the largest member of an $abc$-triple cannot substantially exceed the radical of the product: the three numbers cannot all be built out of high powers of a few small primes at once.
--
--   Waldschmidt states the conjecture in the finiteness form — for each $\varepsilon>0$ only finitely many $abc$-triples satisfy $c > \operatorname{rad}(abc)^{1+\varepsilon}$ — and then records that it is equivalent to the displayed bounded form. The two are interchangeable, but they are not interchangeable *for a fixed* $\varepsilon$: the bounded form at $\varepsilon$ is what yields the finiteness statement at any strictly larger exponent, and conversely the finiteness statement at $\varepsilon$ produces a constant at that same $\varepsilon$ by taking a maximum over the exceptional set. The bounded form is the one in which quantitative work is carried out — the unconditional estimates of Stewart-Tijdeman ($\log c \le \kappa R^{15}$) and Stewart-Yu ($\log c \le \kappa R^{1/3}(\log R)^3$, $R = \operatorname{rad}(abc)$) are bounds of exactly this shape, as is Baker's explicit refinement — and it is the form from which the standard consequences (asymptotic Fermat, Fermat-Catalan, Roth, Szpiro) are usually derived, since they need a numerical bound rather than an unquantified finiteness.
--
--   **Formalization Note.** The coprimality hypothesis is written as `Set.Pairwise` on the set $\{a,b,c\}$, matching the platform statement `ABC_Conjecture` verbatim. The hypothesis $c>0$ is omitted because it follows from $a>0$ and $a+b=c$. The conclusion uses $\le$ rather than the source's strict $<$; the two versions are equivalent, since a constant witnessing one witnesses the other after an arbitrarily small enlargement. The source normalises $abc$-triples by $a<b$; that restriction is dropped here because $\operatorname{rad}(abc)$ and the hypotheses are symmetric in $a$ and $b$, so a constant valid for the normalised triples is valid for all of them.
-- source:
--   Michel Waldschmidt, Lecture on the abc conjecture and some of its consequences, Springer Proceedings in Mathematics and Statistics 98 (2015), 211-230; Section 2 'abc Conjecture', the bulleted statement immediately following Conjecture 2: 'For each eps > 0, there exists kappa(eps) such that, for any abc triple (a,b,c), c < kappa(eps) Rad(abc)^{1+eps}.' Author's preprint: https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/abcLahoreProceedings.pdf . Same statement as the second formulation in https://en.wikipedia.org/wiki/Abc_conjecture (section 'Formulations'). The finiteness form (Waldschmidt Conjecture 2) is the platform statement ABC_Conjecture.

import Mathlib
import Definitions.Def_radicalDM

open scoped BigOperators

namespace ABC

theorem explicit_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c →
        ({a, b, c} : Set ℕ).Pairwise Nat.Coprime →
        (c : ℝ) ≤ K * (radicalDM (a * b * c) : ℝ) ^ (1 + ε) := by sorry

end ABC
