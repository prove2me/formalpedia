-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_Supplement_theorem_1_3
-- name    : ZamirInversion581.Mult.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:53:25.06921+00:00
-- url     : https://prove2.me/theorems/327a284a-a4ea-4cf0-bc7a-3bc91911d426
-- title:
--   Theorem 1.3 — conditional determinant recovery, both parts
-- statement:
--   Fix a finite field $F$ of order $q$ and a trapdoored-matrix family as in §3.1. Let $D$ be one polynomial-time field-RAM program with all-run time bound $T(n)$. Both parts of the conditional determinant theorem hold.
--
--   1. There are $c>0$ and $a\in\mathbb N$, depending only on the field and family, such that for every $\varepsilon>0$, if determinant success on uniform matrices is at least $s_{q,n}+\varepsilon$ for every sufficiently large $n$, worst-case invertibility and exact rank can be computed, for each $0<\kappa\le1/2$, with success probability at least $1-\kappa$ and all-run costs
--   $$
--   c\varepsilon^{-2}(T(n)+n^2)\log(2nEK)^a,\qquad c\varepsilon^{-2}(T(2n)+n^2)\log(2nEK)^a,
--   $$
--   where $E=\lceil1/\varepsilon\rceil$ and $K=\lceil1/\kappa\rceil$.
--
--   2. Suppose $q>2$. For every $\varepsilon>0$ there are $c>0,a\in\mathbb N$, now allowed to depend on $\varepsilon$ as well as the field and family but not on $D,T,\kappa$, with the following property. If $p_n=\Pr[D(Y)=\det Y]\ge1/(q-1)+\varepsilon$ on uniform invertible $Y$ for every sufficiently large $n$, there are preprocessing and recovery programs. Preprocessing sees $n,K$ only, and all its runs halt within $c(T(n)+n^2)\log(2nK)^a$ operations. With probability at least $1-\kappa$, its subgroup $H$ and state are good simultaneously for every future target matrix. A good subgroup is proper and has order $h$ satisfying
--   $$
--   h\mid(q-1),\qquad h<\frac1{p_n-\varepsilon/4}<\min\{q-1,2/\varepsilon\}.
--   $$
--   For every target $A$, recovery using that fixed state halts within the same bound on every run and, with probability at least $1-\kappa$, returns $z\in F$ such that
--   $$
--   zH=(\det A)H,\qquad z^h=(\det A)^h.
--   $$
--   In particular, singular inputs yield the coset $\{0\}$ and $z=0$. All conclusions hold above dimension thresholds that may depend on the algorithm and failure target.
--
--   This companion theorem retains the two distinct determinant thresholds, preprocessing before the target, and the exact subgroup and power conclusions.
--
--   Differences from the source:
--   - reading: polynomial-time determinant algorithm and field-operation time → one finite oracle-free field-RAM program with polynomial all-run time and an arbitrary additional bound T; reason: §3.1 counts field operations; using the same model for trapdoor routines and distinguishers avoids an oracle strengthening
--   - reading: Õ_q in part (i) and Õ_{q,ε} in part (ii) → explicit polylogarithmic bounds with constants before ε in (i), after ε in (ii), and before D,T,κ in both; reason: the subscripts specify exactly these dependencies; hypotheses and conclusions use sufficiently large dimensions
--   - reading: high probability preprocessing and subsequent recovery for every A → a preprocessing event of probability at least 1−κ on which H is proper and satisfies all bounds, and recovery succeeds with probability at least 1−κ for every A; reason: the calibration event on pp.22–24 is independent of the target and supplies one fixed subgroup
--   - encoding: compute det(A)H, equivalently (det A)^h → return a field element z with both coset equality as subsets of F and z^h=(det A)^h; reason: a representative encodes the same coset, includes zero on singular inputs, and retains the equivalent power conclusion
--   - reading: preprocessing fixes H before the input, and 'the reduction computes the coset … in Õ_{q,ε}(T(n)+n²) time' → Pre receives n,K only and returns a subgroup element list and state, subsequently supplied to Rec with A, and every run of Pre obeys the same bound c(T(n)+n²)log(2nK)^a as Rec; reason: the time bound is read as covering the whole reduction including calibration, as p.24 states ('The subgroup calibration and coset recovery require polynomially many samples in 1/ε … This establishes the claimed Õ_{q,ε}(T(n)+n²) running time')
--   - reading: in (i), 'worst-case invertibility is decidable' and 'exact rank follows' with no probability qualifier → correct output with probability at least 1−κ for each 0<κ≤1/2; reason: the reduction is randomized and statistical (pp.20–21, empirical calibration under pseudorandom masks), as in Theorem 1.2's 'with high probability'; an error-free reading is not what the proof gives
--   - reading: hypotheses at dimension n, range of n unstated → for every n ≥ N₀; reason: this is the stronger of the two readings (it is implied by the every-n reading), matching the base goal's 'for all sufficiently large m'; the conclusions are claimed for n ≥ n₀
--   - reading: 'the same trapdoored-matrix assumption' (p.11: samplers indexed by n, Õ(n²) sampling, Õ(n) action) → one sampler program and one action program of the field RAM taking n as input, with constants C, b of the family, and c, a allowed to depend on the family; reason: the reductions are uniform algorithms that draw trapdoored matrices at every dimension (pp.19–24), and the polylogarithmic exponents of the family enter the Õ bounds
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.4, Theorem 1.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Supplement_Reductions

set_option autoImplicit false

namespace ZamirInversion581.Mult.Supplement

/-- Theorem 1.3, p.4, both parts. Calibration is independent of the target matrix.
The constants of (i) precede ε; those of (ii) follow ε but precede D,T,κ. -/
theorem theorem_1_3 (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (𝒯 : TrapdoorPrograms F) (h𝒯 : IsTrapdoored 𝒯) :
    (∃ (c : ℝ) (a : ℕ), 0 < c ∧
      ∀ (ε : ℝ), 0 < ε → ∀ (D : Program F) (T : ℕ → NNReal) (N₀ : ℕ),
        PolyTime D → TimeBound D T →
        (∀ n ≥ N₀, singularity F n + ε ≤ avgSuccess D (fun _ X => detAnswer X) n) →
        ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 → RankAndInvertibility (F := F) c a ε κ T) ∧
    (2 < Fintype.card F → ∀ ε : ℝ, 0 < ε →
      ∃ (c : ℝ) (a : ℕ), 0 < c ∧
        ∀ (D : Program F) (T : ℕ → NNReal) (N₀ : ℕ),
          PolyTime D → TimeBound D T →
          (∀ n ≥ N₀, 1 / (Fintype.card F - 1 : ℝ) + ε ≤ invertibleDetSuccess D n) →
          ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 → CosetRecovery c a ε κ D T) := by sorry

end ZamirInversion581.Mult.Supplement
