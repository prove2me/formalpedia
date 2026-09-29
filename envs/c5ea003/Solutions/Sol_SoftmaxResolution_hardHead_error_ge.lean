-- Prove2me | solution 1 for SoftmaxResolution.hardHead_error_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T01:12:27.215824+00:00
-- url     : https://prove2.me/submissions/b8c1c495-a064-4879-82c8-4aeb9c1f0d2a

-- Sol generated from MachineLearning/TransformerUniversality/SoftmaxResolution.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxResolution

/-!
# Soft selection beats hard selection: refuting the `Ω(1/N)` resolution barrier for softmax heads

`Catalog/MachineLearning/TransformerUniversality/FiniteLookupSeparation.lean` proves that a
*hard* lookup architecture that reads one of `N` stored values has uniform error at least
`1/(2N)` against the identity on `[0,1]`, and that the bound is attained.  The first
next-cycle sub-conjecture of `FUTURE_DIRECTIONS.md` proposed that the same `Ω(1/N)` barrier
survives softmax: *"a softmax attention layer with `N` fixed keys and arbitrary score scale has
uniform error at least `c/N` on the identity."*

**This file refutes that conjecture.**  Softmax weights are strictly interior points of the
simplex and vary continuously with the input, so a *two*-key softmax head with values `0` and
`1` already approximates the identity on `[0,1]` to arbitrary accuracy: choosing the logit
gap `log ((x+ε)/(1+ε-x))` gives the attention weight `(x+ε)/(1+2ε)`, whose distance from `x`
is at most `ε` uniformly on `[0,1]`.  No lower bound of the form `c/N` can therefore hold.

Main results:

* `softmaxHead_le_of_le`, `le_softmaxHead_of_le` — a softmax head always outputs a point of
  the convex hull of its values (the only thing hard and soft selection have in common);
* `logitHead_eq` — the closed form `(x+ε)/(1+2ε)` of the two-key head used below;
* `two_key_softmax_approx_identity` — **`ε`-approximation of the identity on `[0,1]` with two
  keys**, for every `ε > 0`;
* `no_universal_softmax_resolution_bound` — the formal refutation: there is no constant
  `c > 0` with `c/N` uniform error for all `N`-key softmax heads;
* `hardHead_error_ge` — the contrasting hard-selection bound `1/(2N)`, proved here by
  pigeonhole on the `N+1` grid points `k/N` so that the dichotomy is self-contained;
* `soft_hard_dichotomy` — the two statements side by side at `N = 2`: error `≤ ε` for every
  `ε > 0` on the soft side, error `≥ 1/4` unconditionally on the hard side.

The moral for the scope qualification of the original development is that the `Θ(1/N)`
resolution barrier proved in `FiniteLookupSeparation.lean` is an artifact of **hard**
selection — of reading a finite value table — and not of the number of heads or keys.  A
genuine lower bound for softmax models must therefore constrain the score family (e.g. to
bilinear scores), not merely count keys.
-/

open scoped BigOperators

open SoftmaxResolution


variable {ι : Type*} [Fintype ι] [Nonempty ι]























open SoftmaxResolution in
theorem solution{N : ℕ} (hN : 0 < N) (sel : ℝ → Fin N) (v : Fin N → ℝ) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) / (2 * N) ≤ |hardHead sel v x - x| := by
  by_contra hcon
  push_neg at hcon
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmem : ∀ k : Fin (N + 1), ((k : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNR]
    have : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
    exact_mod_cast this
  obtain ⟨k, l, hkl, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (N + 1) => sel ((k : ℝ) / N)) (by simp)
  have h1 := hcon _ (hmem k)
  have h2 := hcon _ (hmem l)
  simp only [hardHead] at h1 h2
  rw [heq] at h1
  have hdist : |((k : ℝ) / N) - ((l : ℝ) / N)| < 1 / N := by
    calc |((k : ℝ) / N) - ((l : ℝ) / N)|
        ≤ |v (sel ((l : ℝ) / N)) - (k : ℝ) / N| + |v (sel ((l : ℝ) / N)) - (l : ℝ) / N| := by
          rw [abs_sub_comm (v (sel ((l : ℝ) / N))) ((k : ℝ) / N)]
          exact abs_sub_le _ _ _
      _ < 1 / (2 * N) + 1 / (2 * N) := by linarith
      _ = 1 / N := by field_simp; ring
  have hklR : (k : ℕ) ≠ (l : ℕ) := fun h => hkl (Fin.ext h)
  have hlow : (1 : ℝ) / N ≤ |((k : ℝ) / N) - ((l : ℝ) / N)| := by
    have h1' : (1 : ℝ) ≤ |((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)| := by
      rcases lt_or_gt_of_ne hklR with hlt | hlt
      · have hle : (((k : ℕ) : ℝ)) + 1 ≤ ((l : ℕ) : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hle : (((l : ℕ) : ℝ)) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonneg (by linarith)]
        linarith
    rw [div_sub_div_same, abs_div, abs_of_pos hNR]
    gcongr
  linarith
