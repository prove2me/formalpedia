-- Prove2me | solution 1 for NormalityConverse.intervalEquidistributed_of_bAdic_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:53:54.61117+00:00
-- url     : https://prove2.me/submissions/c2fc894e-4017-4535-9312-c04c9c94ebf2

-- Sol generated from NumberTheory/NormalityConverse.lean
import Mathlib
import Definitions.Def_NumberTheory_NormalityConverse

/-!
# Aligned-cylinder frequencies and interval equidistribution

This file formalizes the approximation step in the converse normality criterion.
An arbitrary interval is squeezed between aligned base-`b` intervals whose lengths
approach its length.  Convergence of the two aligned-interval frequencies then
forces convergence of the arbitrary interval frequency.
-/

open NormalityConverse

open Filter Set
open scoped Topology










/-- Empirical frequency is monotone under inclusion of predicates. -/
lemma empiricalFrequency_mono {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ n, P n → Q n) (N : ℕ) :
    empiricalFrequency P N ≤ empiricalFrequency Q N := by
  unfold empiricalFrequency
  gcongr
  exact hPQ _








open NormalityConverse in
theorem solution    {b : ℕ} (u : ℕ → ℝ) (h : HasBAdicSandwichFrequencies b u) :
    IntervalEquidistributed u := by
  intro a c ha hc hc1
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Use the sandwich hypothesis with ε / 2
  obtain ⟨k, Ai, Ci, Ao, Co, hAiCi, hCi_bk, hAoCo, hCo_bk,
           hinner, houter, hinner_len, houter_len, htend_inner, htend_outer⟩ :=
    h a c ha hc hc1 (ε / 2) (half_pos hε)
  -- Get N for inner sequence with ε / 4 tolerance
  have hε4 : ε / 4 > 0 := by linarith
  rw [Metric.tendsto_atTop] at htend_inner htend_outer
  obtain ⟨N_inner, hN_inner⟩ := htend_inner (ε / 4) hε4
  obtain ⟨N_outer, hN_outer⟩ := htend_outer (ε / 4) hε4
  use max N_inner N_outer
  intro n hn
  have hn_inner : n ≥ N_inner := le_trans (le_max_left _ _) hn
  have hn_outer : n ≥ N_outer := le_trans (le_max_right _ _) hn
  have hin_inner := hN_inner n hn_inner
  have hin_outer := hN_outer n hn_outer
  -- Apply monotonicity
  have hmono_inner : empiricalFrequency (fun n => u n ∈ Ico ((Ai : ℝ) / (b : ℝ) ^ k) ((Ci : ℝ) / (b : ℝ) ^ k)) n ≤
                     empiricalFrequency (fun n => u n ∈ Ico a c) n :=
    empiricalFrequency_mono (fun n h => hinner h) n
  have hmono_outer : empiricalFrequency (fun n => u n ∈ Ico a c) n ≤
                     empiricalFrequency (fun n => u n ∈ Ico ((Ao : ℝ) / (b : ℝ) ^ k) ((Co : ℝ) / (b : ℝ) ^ k)) n :=
    empiricalFrequency_mono (fun n h => houter h) n
  -- Extract bound values from distances
  rw [Real.dist_eq] at hin_inner hin_outer
  rw [abs_lt] at hin_inner hin_outer
  -- hin_inner : -ε/4 < inner_freq - inner_len ∧ inner_freq - inner_len < ε/4
  -- hin_outer : -ε/4 < outer_freq - outer_len ∧ outer_freq - outer_len < ε/4
  set infreq := empiricalFrequency (fun n => u n ∈ Ico ((Ai : ℝ) / (b : ℝ) ^ k) ((Ci : ℝ) / (b : ℝ) ^ k)) n with hinfreq_def
  set outfreq := empiricalFrequency (fun n => u n ∈ Ico ((Ao : ℝ) / (b : ℝ) ^ k) ((Co : ℝ) / (b : ℝ) ^ k)) n with houtfreq_def
  set midfreq := empiricalFrequency (fun n => u n ∈ Ico a c) n with hmidfreq_def
  set inlen := ((Ci : ℝ) - Ai) / (b : ℝ) ^ k with hinlen_def
  set outlen := ((Co : ℝ) - Ao) / (b : ℝ) ^ k with houtlen_def
  -- From hin_inner: inlen - ε/4 < infreq < inlen + ε/4
  have hinfreq_lower : infreq > inlen - ε / 4 := by linarith [hin_inner.1]
  have hinfreq_upper : infreq < inlen + ε / 4 := by linarith [hin_inner.2]
  -- From hin_outer: outlen - ε/4 < outfreq < outlen + ε/4
  have houtfreq_lower : outfreq > outlen - ε / 4 := by linarith [hin_outer.1]
  have houtfreq_upper : outfreq < outlen + ε / 4 := by linarith [hin_outer.2]
  -- From hinner_len: (c - a) - ε/2 < inlen
  have hinlen_lower : inlen > (c - a) - ε / 2 := hinner_len
  -- From houter_len: outlen < (c - a) + ε/2
  have houtlen_upper : outlen < (c - a) + ε / 2 := houter_len
  -- Combine bounds: midfreq > (c - a) - 3ε/4 and midfreq < (c - a) + 3ε/4
  have hmid_lower : midfreq > (c - a) - 3 * ε / 4 := by linarith
  have hmid_upper : midfreq < (c - a) + 3 * ε / 4 := by linarith
  -- Therefore dist midfreq (c - a) < ε
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith
