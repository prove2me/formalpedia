-- Prove2me | solution 1 for Catalog.Novelty.KVDecisionDissociation.diffuse_decision_is_fragile
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:04:59.428133+00:00
-- url     : https://prove2.me/submissions/7fe48657-34f0-413f-876c-f697af531af6

-- Sol generated from Novelty/KVDecisionDissociation.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation

/-!
# Decision–vector dissociation for attention scores (NET-51, Part A)

This file formalises the *structural* content of the NET-51 measurement
**THE-KV-CORE-IS-SHARED-THE-TAIL-IS-PERSONAL**.

The empirical situation was: two fine-tunes of the same base transformer keep
cosine-similar key/value caches at *every* layer (`cosK ≥ 0.976`, mean `0.990`),
yet in the last two layers (L22/L23) their top-1 attention decisions agree only
`0.568` / `0.627` of the time.  The slogan extracted from that measurement is

> *vector similarity does not bound functional divergence.*

Here we prove that this is not an artefact of one model pair but a theorem
about score vectors:

* `strictTop_of_margin` — the *correct* stability certificate is a **margin**
  (gap) condition: if the top-1 gap of `u` exceeds `2ε` and `u` and `v` differ
  by at most `ε` coordinatewise, then `v` makes the same decision.
* `margin_factor_two_is_sharp` — the constant `2` cannot be improved: with gap
  exactly `2ε` a perturbation of size `ε` can already destroy the decision.
* `cosine_near_one_decision_flip` — for **every** `ε > 0` there are two score
  vectors with cosine similarity `> 1 - ε` whose top-1 decisions differ.  So no
  function of the cosine alone can lower-bound decision agreement: this is the
  NET-51 dissociation, in its sharpest possible form.
* `strictTop_le_sqrt_collision` / `diffuse_decision_is_fragile` — the
  quantitative reason the *diffuse* tail is where decisions break: a small
  collision mass `∑ p k ^ 2` forces a small top-1 gap, hence a flip under an
  arbitrarily small perturbation.

Nothing here is asymptotic or approximate: all constants are explicit.
-/

open Catalog.Novelty.KVDecisionDissociation

open Finset



/-! ### 1. The correct stability certificate: margin, not cosine -/



/-! ### 2. Cosine similarity: the dissociation -/








/-! ### 3. Why the *diffuse* tail is the fragile region -/

/-- Any coordinate of a nonnegative vector is bounded by the square root of its
collision mass `∑ p k ^ 2`.  For an attention distribution this says: diffuse
(low-collision) attention has a small top weight. -/
theorem strictTop_le_sqrt_collision {n : ℕ} (p : Fin n → ℝ) (hp : ∀ k, 0 ≤ p k)
    (i : Fin n) : p i ≤ Real.sqrt (∑ k, p k ^ 2) := by
  have h1 : p i ^ 2 ≤ ∑ k, p k ^ 2 :=
    Finset.single_le_sum (f := fun k => p k ^ 2) (fun k _ => sq_nonneg (p k)) (mem_univ i)
  calc p i = Real.sqrt (p i ^ 2) := (Real.sqrt_sq (hp i)).symm
    _ ≤ Real.sqrt (∑ k, p k ^ 2) := Real.sqrt_le_sqrt h1


/-! ### 4. The two halves put together

`core_layers_agree` is the positive half (a margin certificate makes *all*
per-layer decisions agree, which is what the 22 shared layers exhibit) and
`cosine_near_one_decision_flip` is the negative half (cosine alone certifies
nothing, which is what the tail exhibits). -/



open Catalog.Novelty.KVDecisionDissociation in
theorem solution{n : ℕ} (p : Fin n → ℝ) (hp : ∀ k, 0 ≤ p k)
    (i j : Fin n) (hij : j ≠ i) (htop : IsStrictTop p i) (eta : ℝ) (heta : 0 < eta) :
    ∃ q : Fin n → ℝ,
      (∀ k, |p k - q k| ≤ Real.sqrt (∑ k, p k ^ 2) + eta) ∧ IsStrictTop q j := by
  refine ⟨Function.update p j (p i + eta), ?_, ?_⟩
  · intro k
    by_cases hk : k = j
    · subst hk
      have hpk : p k < p i := htop k hij
      have h1 : |p k - (p i + eta)| = p i + eta - p k := by
        rw [abs_of_nonpos (by linarith)]; ring
      have h2 : p i ≤ Real.sqrt (∑ k, p k ^ 2) := strictTop_le_sqrt_collision p hp i
      have h3 : 0 ≤ p k := hp k
      simp only [Function.update_self, h1]
      linarith
    · have hnn : 0 ≤ Real.sqrt (∑ k, p k ^ 2) := Real.sqrt_nonneg _
      simp [Function.update_of_ne hk]
      linarith
  · intro k hk
    have hle : p k ≤ p i := by
      by_cases h : k = i
      · exact le_of_eq (by rw [h])
      · exact (htop k h).le
    simp only [Function.update_self, Function.update_of_ne hk]
    linarith
