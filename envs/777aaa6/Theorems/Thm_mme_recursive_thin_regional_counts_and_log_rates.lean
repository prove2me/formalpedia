-- Prove2me | Theorems.Thm_mme_recursive_thin_regional_counts_and_log_rates
-- name    : mme_recursive_thin_regional_counts_and_log_rates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T15:39:36.923965+00:00
-- url     : https://prove2.me/theorems/4143f4bc-f657-470b-8ceb-e9bed9ad8976
-- title:
--   Exact thin regional family, all-mode degrees, and classical entropy rate
-- statement:
--   Let $h,R\in\mathbb N$. For every region $r\in[R]=\{0,\ldots,R-1\}$, choose a parent vector $P_r\in\mathbb N^3$ with at least one coordinate at most $1$. Its split alphabet is
--   $$
--   A_r=\{a\in\{0,\ldots,h\}^3:a_X+a_Y+a_Z=h,\ a_i\le P_{r,i}\text{ for every }i\}.
--   $$
--   Choose arbitrary integer split counts $m_r:A_r\to\mathbb N$, and set
--   $$
--   M_{r,i,j}=\sum_{a\in A_r:a_i=j}m_r(a),\qquad n_r(t)=t\sum_{a\in A_r}m_r(a).
--   $$
--   An address is a tuple $w=(w_r)_r$ with $w_r:[n_r(t)]\to A_r$. Let $\mathcal A_t$ be all addresses whose three coordinate histograms in each region are $tM_{r,i,j}$, and let $\mathcal T_t$ be the addresses with exact joint histograms $tm_r$. The mode-$i$ block of $w$ is the full tuple of coordinate words $(w_r(\cdot)_i)_r$; regions are never merged.
--
--   For every $t\ge0$, the thin-parent condition gives $\mathcal A_t=\mathcal T_t\ne\varnothing$. Define
--   $$
--   T(t)=\prod_r\binom{n_r(t)}{(t m_r(a))_{a\in A_r}},\qquad
--   B_i(t)=\prod_r\binom{n_r(t)}{(tM_{r,i,j})_{j=0}^h},
--   $$
--   $$
--   D_i(t)=\prod_r\prod_{j=0}^h
--   \frac{(tM_{r,i,j})!}{\prod_{a\in A_r:a_i=j}(t m_r(a))!}.
--   $$
--   These are exact natural-number counts: $|\mathcal A_t|=T(t)$; the number of distinct mode-$i$ blocks is $B_i(t)$; and every mode-$i$ block present in $\mathcal A_t$ has exactly $D_i(t)$ preimages, including the address itself. In particular,
--   $$
--   T(t)=B_i(t)D_i(t)\qquad(i=X,Y,Z).
--   $$
--   Using natural logarithms and $0\log0=0$, write
--   $$
--   \mathsf H(v)=\Bigl(\sum_jv_j\Bigr)\log\Bigl(\sum_jv_j\Bigr)-\sum_jv_j\log v_j,
--   \qquad H=\sum_r\mathsf H(m_r),\qquad H_i=\sum_r\mathsf H(M_{r,i,\cdot}).
--   $$
--   Then, as the integer scale $t\to\infty$,
--   $$
--   \frac{\log T(t)}t\to H,\qquad
--   \frac{\log B_i(t)}t\to H_i,\qquad
--   \frac{\log D_i(t)}t\to H-H_i.
--   $$
--   Consequently,
--   $$
--   \frac{\log\max_iD_i(t)}t\to\max_i(H-H_i),\qquad
--   \frac{\log T(t)-\log\max_iD_i(t)}t\to\min_i H_i.
--   $$
--   The final expression is the minimum of the three sums over regions, not the sum of regionwise minima. Zero counts and empty regions are allowed. This theorem proves the actual finite family and all-mode degree formulas and their asymptotic counting rates; it does not by itself assert a hashing choice, an induced matching, a tensor restriction, or a component-value estimate.
-- source:
--   Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Sections 3.6–3.7 (type counts and entropy estimates) and Section 7.1 (recursive regions and parent types). Derived generic classical thin-parent counting/rate lemma. Uses the proved mme_recursive_x_hash_family_counts, mme_recursive_thin_split_marginal_joint_counts, mme_fintype_constrained_prescribed_fiber_function_card, and mme_scaled_multinomial_log_rate; not a verbatim numbered theorem of the paper.

import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false

theorem mme_recursive_thin_regional_counts_and_log_rates
    (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (m : ∀ r, Split half (parent r) → ℕ) :
    let M : Fin R → Fin 3 → Fin (half + 1) → ℕ := fun r i j ↦
      ∑ a : {a : Split half (parent r) // a.val i = j}, m r a.val
    let n : ℕ → Fin R → ℕ := fun t r ↦ (∑ a, m r a) * t
    let mt : ∀ t r, Split half (parent r) → ℕ := fun t r a ↦ m r a * t
    let T : ℕ → ℕ := fun t ↦ ∏ r, Nat.multinomial Finset.univ (mt t r)
    let B : ℕ → Fin 3 → ℕ := fun t i ↦ ∏ r,
      Nat.multinomial Finset.univ (fun j ↦ M r i j * t)
    let Deg : ℕ → Fin 3 → ℕ := fun t i ↦ ∏ r, ∏ j,
      (M r i j * t).factorial /
        ∏ a : {a : Split half (parent r) // a.val i = j}, (mt t r a.val).factorial
    let H : ℝ := ∑ r, (
      ((∑ a, m r a : ℕ) : ℝ) * Real.log ((∑ a, m r a : ℕ) : ℝ) -
        ∑ a, (m r a : ℝ) * Real.log (m r a : ℝ))
    let HM : Fin 3 → ℝ := fun i ↦ ∑ r, (
      ((∑ j, M r i j : ℕ) : ℝ) * Real.log ((∑ j, M r i j : ℕ) : ℝ) -
        ∑ j, (M r i j : ℝ) * Real.log (M r i j : ℝ))
    let maxDeg : ℕ → ℕ := fun t ↦ max (max (Deg t 0) (Deg t 1)) (Deg t 2)
    (∀ t : ℕ,
      ambient (n := n t) (mt t) = target (n := n t) (mt t) ∧
      (target (n := n t) (mt t)).Nonempty ∧
      (ambient (n := n t) (mt t)).card = T t ∧
      ∀ i : Fin 3,
        ((ambient (n := n t) (mt t)).image (block i)).card = B t i ∧
        T t = B t i * Deg t i ∧
        ∀ a ∈ ambient (n := n t) (mt t),
          ((ambient (n := n t) (mt t)).filter (fun b ↦ block i b = block i a)).card =
            Deg t i) ∧
    Tendsto (fun t : ℕ ↦ Real.log (T t : ℝ) / (t : ℝ)) atTop (𝓝 H) ∧
    (∀ i : Fin 3,
      Tendsto (fun t : ℕ ↦ Real.log (B t i : ℝ) / (t : ℝ)) atTop (𝓝 (HM i)) ∧
      Tendsto (fun t : ℕ ↦ Real.log (Deg t i : ℝ) / (t : ℝ)) atTop (𝓝 (H - HM i))) ∧
    Tendsto (fun t : ℕ ↦ Real.log (maxDeg t : ℝ) / (t : ℝ))
      atTop (𝓝 (max (max (H - HM 0) (H - HM 1)) (H - HM 2))) ∧
    Tendsto (fun t : ℕ ↦ (Real.log (T t : ℝ) - Real.log (maxDeg t : ℝ)) / (t : ℝ))
      atTop (𝓝 (min (min (HM 0) (HM 1)) (HM 2))) := by sorry
