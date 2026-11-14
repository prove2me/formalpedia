-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_event_exponential_reduction
-- name    : ZeroFreeRRG.Hardcore.overlap_event_exponential_reduction
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:58:03.841204+00:00
-- url     : https://prove2.me/theorems/f1cd3f78-f000-4f4a-9062-5dc68251abb7
-- title:
--   Exponential overlap bound from reveal concentration and density tails
-- statement:
--   For a sequence of finite spaces with nonnegative weights $p_n,q_n$, suppose the revealed deviation event has exponentially small $q_n$-weight, the target deviation outside that event has exponentially small $p_n$-weight, and the bad-density event has exponentially small $p_n$-weight. If on the remaining revealed event the density ratio is at most $e^{bn/2}$ while the first two concentration rates are $b>0$, then the target deviation has $p_n$-weight at most $e^{-rn}$ for some $r>0$ and all sufficiently large admissible $n$. This packages the final decomposition in Lemma 5.6.
-- source:
--   Auxiliary reduction in Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, pp. 39–40, proof of Lemma 5.6.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.overlap_event_exponential_reduction (Ω : ℕ → Type) [∀ n, Fintype (Ω n)]
    (p q : ∀ n, Ω n → ℝ) (D H Good : ∀ n, Ω n → Prop) (admissible : ℕ → Prop)
    (A B C b c : ℝ) (N₀ : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : 0 < b) (hc : 0 < c)
    (hp : ∀ n x, 0 ≤ p n x) (hq : ∀ n x, 0 ≤ q n x)
    (hdens : ∀ n ≥ N₀, admissible n → ∀ x, H n x → Good n x → p n x ≤ Real.exp (b*n/2)*q n x)
    (hmiss : ∀ n ≥ N₀, admissible n → (∑ x, if D n x ∧ ¬ H n x then p n x else 0) ≤ A*Real.exp (-b*n))
    (hreference : ∀ n ≥ N₀, admissible n → (∑ x, if H n x then q n x else 0) ≤ B*Real.exp (-b*n))
    (htail : ∀ n ≥ N₀, admissible n → (∑ x, if ¬ Good n x then p n x else 0) ≤ C*Real.exp (-c*n)) :
    ∃ r : ℝ, 0 < r ∧ ∃ N : ℕ, ∀ n ≥ N, admissible n →
      (∑ x, if D n x then p n x else 0) ≤ Real.exp (-r*n) := by sorry
