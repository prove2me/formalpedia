-- Prove2me | Theorems.Thm_cube_alt_sum_to_sensitivity_univ
-- name    : cube_alt_sum_to_sensitivity_univ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-06T22:06:51.665072+00:00
-- url     : https://prove2.me/theorems/150c2fbd-57dc-4515-a7e6-7ff4f249e6cd
-- statement:
--   **Alternating sum on the full $d$-cube $\Rightarrow$ sensitivity bound.**
--
--   Let $h : \mathbb{N} \to \mathbb{R}$ be monotone, and suppose that for every $m \ge 1$ and every set $S \subseteq Q_m$ of vertices of the $m$-cube with $|S| > 2^{m-1}$, there is $v \in S$ with internal degree $\deg_S(v) \ge h(m)$. Then for every $d \ge 1$ and every Boolean function $g : \{0,1\}^d \to \{0,1\}$ whose Möbius alternating sum on the *full* index set is non-zero,
--   $$\sum_{T \subseteq \{1,\ldots,d\}} (-1)^{d - |T|} \cdot \mathbf{1}\!\left[ g(\chi_T) \right] \;\ne\; 0,$$
--   we have
--   $$h(d) \;\le\; s(g),$$
--   where $\chi_T \in \{0,1\}^d$ is the indicator of $T$ and $s(g)$ is the sensitivity.
--
--   This is the *core* combinatorial lemma of the Gotsman–Linial parity step, with the sub-cube reindexing stripped away. The general case (alt-sum on an arbitrary $S \subseteq \{1,\ldots,n\}$) reduces to this via $\mathrm{Finset.orderEmbOfFin}$.
--
--   Sketch: parity-split the alternating sum as $(-1)^d \cdot (A - B)$ where $A = \#\{z : g(z) = 1, \, |z| \text{ even}\}$ and $B = \#\{z : g(z) = 1, \, |z| \text{ odd}\}$. Non-zero gives $A \ne B$; WLOG $A > B$. Form $H = \{z : g(z) = 1, \, |z| \text{ even}\} \cup \{z : g(z) = 0, \, |z| \text{ odd}\}$, which (using $\#\{z : |z| \text{ even}\} = 2^{d-1}$) has $|H| = 2^{d-1} + (A - B) > 2^{d-1}$. Apply $\mathrm{hQ}$ at $m = d$ to get $v \in H$ with $\deg_H(v) \ge h(d)$. A parity case-analysis on the neighbour gives $\deg_H(v) = \mathrm{sens}_g(v) \le s(g)$.
-- source:
--   Gotsman, Chaim, and Nathan Linial. "The equivalence of two problems on the cube." Journal of Combinatorial Theory, Series A 61.1 (1992): 142-146. (Direction used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Definitions.Def_Hypercube
import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

/-!
# d-cube alternating-sum ⇒ sensitivity bound

Specialised to `Finset.univ : Finset (Fin d)`. If `g : BoolFunc d` has
non-zero top Möbius alternating sum, then `h d ≤ sensitivity g`. This is
the "core" Gotsman–Linial parity step, with the sub-cube bridge stripped
away — the parent theorem `bool_func_alternating_sum_sensitivity`
reduces to this via `Finset.orderEmbOfFin`.

Proof outline (in the sketch):
- Parity-split the alternating sum: it equals `(-1)^d · (A − B)` where
  `A := #{z : g z = true ∧ |z| even}`, `B := #{z : g z = true ∧ |z| odd}`.
  Hence `A ≠ B`.
- WLOG `A > B`. Define the "parity-aligned" majority set
  `H := {z : g z = true ∧ |z| even} ∪ {z : g z = false ∧ |z| odd}`.
  Then `|H| = 2^(d-1) + (A − B) > 2^(d-1)`.
- Apply `hQ` at `m = d` to pick `v ∈ H` with `h d ≤ degreeIn d H v`.
- For `v ∈ H`, every neighbour `u` of `v` satisfies `u ∈ H ↔ g u ≠ g v`
  (parity flips when one bit is flipped). Hence
  `degreeIn d H v = sensitivityAt g v ≤ sensitivity g`.
-/

/-- **d-cube alternating-sum ⇒ sensitivity bound.** If `g : BoolFunc d`
    with `d ≥ 1` has a non-zero Möbius alternating sum on
    `Finset.univ : Finset (Fin d)`, then `h d ≤ sensitivity g`. -/

theorem cube_alt_sum_to_sensitivity_univ
    (h : ℕ → ℝ) (hmono : Monotone h)
    (hQ : ∀ m, 0 < m → ∀ S : Finset (Fin m → Bool),
        2 ^ (m - 1) < S.card →
          ∃ v ∈ S, h m ≤ (Hypercube.degreeIn m S v : ℝ))
    {d : ℕ} (h_pos : 1 ≤ d) (g : BoolFunc d)
    (h_alt :
      (∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          (if (d - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if g (fun i => decide (i ∈ T)) then (1 : ℝ) else 0))
        ≠ 0) :
    h d ≤ (sensitivity g : ℝ) := by sorry
