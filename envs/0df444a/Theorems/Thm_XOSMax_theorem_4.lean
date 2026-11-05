-- Prove2me | Theorems.Thm_XOSMax_theorem_4
-- name    : XOSMax.theorem_4
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:28:53.719236+00:00
-- url     : https://prove2.me/theorems/86c6d5bb-ff90-43b0-8afd-081981ab2e94
-- title:
--   Theorem 4 — a $(k-1)$-maximizer of every $k$-XOS function in $O(k^2n)$ time, exactly when $k=2$
-- statement:
--   There is an absolute constant $C$ with the following property. Let $V$ be a nonempty finite ground set of size $n$, and let $L$ be any enumeration of $V$ without repetition. Let $\mathcal A$ be the deterministic value-oracle algorithm that receives $L$, removes the elements with $f(v)\le0$ and runs Algorithm 4. For every $k\ge2$ and every $k$-XOS function $f$ on $V$, with clauses of any sign, writing $\tilde X$ for the output of $\mathcal A$ on $f$:
--
--   1. $\tilde X$ is a $(k-1)$-maximizer of $f$;
--   2. the cost of $\mathcal A$ on $f$ is at most $C\,k^2\,n$;
--   3. if $k=2$, then $\tilde X$ is an exact maximizer of $f$ and the cost is at most $C\,n$.
--
--   The algorithm receives neither $k$ nor a description of $f$: it accesses $f$ only through a value oracle, and one and the same algorithm and constant serve every $k$.
--
--   The ratio $k-1$ is optimal for $k\ge3$ by Theorem 5 of the paper, which is outside this mission.
--
--   Differences from the source:
--   - generalization: there exists a deterministic algorithm → the concrete program `xosMax L`, for every enumeration `L` of the ground set; reason: a statement about the witness implies the existence claim
--   - reading: "time" → value oracle calls plus charged elementary steps of the program; reason: §1, p.2 counts oracle calls and the proof of Lemma 11 also counts set constructions, so this bounds both
--   - encoding: the ground set $V$, "pick", "foreach" and "$\tilde X\in\arg\max$" → a `Fintype E` with `Nonempty E` in `Type`, list order, and the first best candidate in Line 10; reason: every finite set has a copy in `Type`, and the choices are free in the paper
--   - encoding: the instance with no element of $f(v)>0$, implicit in the paper → the output $\emptyset$; reason: then $f(X)\le0=f(\emptyset)$ for every $X$, so $\emptyset$ is a maximizer
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 4, p.2

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_xosMax

namespace XOSMax

open OracleProg

/-- **Theorem 4**: "There exists a deterministic algorithm to find a (k − 1)-maximizer of a given
k-XOS function in O(k²n) time for any k ≥ 2 (even if k is unknown). In particular, when k = 2, it
finds an exact maximizer in O(n) time" (Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3,
Theorem 4, p.2).

**Formalization Note** The algorithm is the program `xosMax L` for an arbitrary enumeration `L` of the
ground set, which implies the existence claim. It is deterministic and does not know `k` because it is
a value of the program type built from `L` alone, and the same program serves every `k`. `O(·)` is one
constant `C`, chosen before the ground set, `L`, `k` and `f`. The cost counts value oracle calls and
charged elementary steps. There is no hypothesis on the sign of `f` or of the clauses: the §2
preprocessing inside `xosMax` discharges `f(v) > 0`. -/
theorem theorem_4 : ∃ C : ℕ, ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (L : List E),
    L.Nodup → (∀ v, v ∈ L) → ∀ (k : ℕ), 2 ≤ k → ∀ f : Finset E → ℝ, IsKXOS k f →
      IsMaximizerApprox Finset.univ ((k : ℝ) - 1) f (run f (xosMax L)).1 ∧
      (run f (xosMax L)).2 ≤ C * k ^ 2 * Fintype.card E ∧
      (k = 2 → (∀ X, f X ≤ f (run f (xosMax L)).1) ∧
        (run f (xosMax L)).2 ≤ C * Fintype.card E) := by sorry

end XOSMax
