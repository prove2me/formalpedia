-- Prove2me | Theorems.Thm_bool_func_alternating_sum_sensitivity
-- name    : bool_func_alternating_sum_sensitivity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-06T20:39:36.705996+00:00
-- url     : https://prove2.me/theorems/e8b83a16-de12-41a9-b342-3e9a8f1caa1a
-- statement:
--   **Alternating sum $\Rightarrow$ sensitivity bound (Gotsman–Linial parity step).**
--
--   Let $h : \mathbb{N} \to \mathbb{R}$ be monotone, and suppose that for every $m \ge 1$ and every $S \subseteq Q_m$ with $|S| > 2^{m-1}$, there is $v \in S$ with $\deg_S(v) \ge h(m)$. Then for every Boolean function $f : \{0,1\}^n \to \{0,1\}$ and every non-empty $S \subseteq \{1, \ldots, n\}$ whose Möbius alternating sum
--   $$\sum_{T \subseteq S} (-1)^{|S| - |T|} \cdot \mathbf{1}\!\left[ f(\chi_T) \right] \;\ne\; 0,$$
--   we have
--   $$h(|S|) \;\le\; s(f).$$
--
--   This is the combinatorial half of Gotsman–Linial 1992. Sketch of proof: restrict $f$ to the $S$-subcube to obtain a function $g : \{0,1\}^{|S|} \to \{0,1\}$ whose top alternating sum is non-zero. Let $A = \#\{z : g(z) = 1, \, |z| \text{ even}\}$ and $B = \#\{z : g(z) = 1, \, |z| \text{ odd}\}$. The non-zero alternating sum gives $A \ne B$; WLOG $A > B$. Form the parity-aligned majority subset $H = \{z : g(z) = 1, \, |z| \text{ even}\} \cup \{z : g(z) = 0, \, |z| \text{ odd}\}$, which has $|H| = 2^{|S|-1} + (A - B) > 2^{|S|-1}$. Apply $\mathrm{hQ}$ at $m = |S|$ to obtain $v \in H$ with $\deg_H(v) \ge h(|S|)$; a parity case-analysis on the neighbour shows $\deg_H(v) = \mathrm{sens}_g(v)$, which lifts to $f$ via the $S$-extension.
-- source:
--   Gotsman, Chaim, and Nathan Linial. "The equivalence of two problems on the cube." Journal of Combinatorial Theory, Series A 61.1 (1992): 142-146. (Direction used in Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.)

import Definitions.Def_Hypercube
import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

/-!
# Alternating-sum ⇒ sensitivity bound (Gotsman–Linial parity step)

If `f : BoolFunc n` has a non-zero Möbius alternating sum on some
`S ⊆ Fin n` with `|S| ≥ 1`, then `sensitivity f` is bounded below by
`h |S|`, given the hypercube max-degree hypothesis `hQ`.

This is the combinatorial half of Gotsman–Linial 1992. The proof
restricts `f` to the `S`-subcube (via `Finset.orderIsoOfFin`) to get
a Boolean function `g : BoolFunc S.card` with non-zero top
alternating sum, then builds the parity-aligned majority subset
`H ⊆ {0,1}^|S|` of size `> 2^(|S|-1)` and applies `hQ`. The
`H`-degree of any `v ∈ H` equals the local sensitivity of `g` at `v`,
which lifts to the local sensitivity of `f` at the `S`-extension of
`v`.

Stating this directly on `f` (instead of on the restricted `g`)
spares downstream consumers the bijection bookkeeping.
-/

/-- **Alternating-sum ⇒ sensitivity bound (parity step of GL 1992).**
    If `f : BoolFunc n` has a non-zero Möbius alternating sum on some
    non-empty index set `S`, then `h |S| ≤ sensitivity f`. -/

theorem bool_func_alternating_sum_sensitivity
    (h : ℕ → ℝ) (hmono : Monotone h)
    (hQ : ∀ m, 0 < m → ∀ S : Finset (Fin m → Bool),
        2 ^ (m - 1) < S.card →
          ∃ v ∈ S, h m ≤ (Hypercube.degreeIn m S v : ℝ))
    {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n))
    (h_pos : 1 ≤ S.card)
    (h_alt :
      (∑ T ∈ S.powerset,
          (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if f (fun i => decide (i ∈ T)) then (1 : ℝ) else 0))
        ≠ 0) :
    h S.card ≤ (sensitivity f : ℝ) := by sorry
