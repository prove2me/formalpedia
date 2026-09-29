-- Prove2me | solution 1 for SpikeOrigin.card_band_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:04:35.303944+00:00
-- url     : https://prove2.me/submissions/828b568e-d709-44b5-8703-6f49b21857cd

-- Sol generated from Cryptography/SpikeOriginSharp.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
/-
# Sharp constants and the deterministic band histogram

Continuation of `Cryptography.SpikeOriginDegeneracy`, `…Bands`, `…Counting`.

Two further steps of the programme:

* **Sharp discrete degeneracy constant.**  The degeneracy of the "`v ≥ 2⁹⁵`" clause was
  proved above for the first decile `u ≲ 0.1`.  Here it is pushed to `u ≤ 0.1123`
  (`sharp_degeneracy`), which is essentially the continuum optimum
  `(√6 − 2)/4 = 0.11237…`, and shown to be impossible beyond `u = 0.2072`
  (`sharp_constant_witness`) — the other continuum endpoint being
  `(√2 − 1)/2 = 0.20711…`.  So the exact discrete threshold is bracketed by the same two
  quadratic irrationalities that bound the crossing curve (`discrete_threshold_bracket`).

* **Deterministic band histogram.**  Because the residue is strictly increasing, the number
  of window positions with `bitlen v ≤ b` is an explicit difference of integer square roots
  (`card_sizeLe`), and the individual band populations telescope (`card_band_succ`,
  `card_band_formula`).  The band decomposition of a Fermat window carries no stochastic
  content at all: it is a function of `N` alone.
-/

open SpikeOrigin

/-! ## Sharp constant for the degeneracy -/




/-! ## Deterministic band histogram -/





theorem solution(N b : ℕ) :
    ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
        (fun j => (resid N j).size ≤ b)).card
      + ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
        (fun j => (resid N j).size = b + 1)).card
      = ((Finset.Ioc (Nat.sqrt N) (3 * Nat.sqrt N)).filter
        (fun j => (resid N j).size ≤ b + 1)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩) <;> exact ⟨hx, by omega⟩
    · rintro ⟨hx, h⟩
      rcases Nat.lt_or_ge (resid N x).size (b + 1) with h' | h'
      · exact Or.inl ⟨hx, by omega⟩
      · exact Or.inr ⟨hx, by omega⟩
  · rw [Finset.disjoint_left]
    rintro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    omega
