-- Prove2me | solution 1 for FactoringBarriers.dft_sample_count_ge_period
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:36:15.346122+00:00
-- url     : https://prove2.me/submissions/7859c034-8bbc-4d4e-a366-0b4de6fb4178

-- Sol generated from Cryptography/FactoringBarriers/DFTSampleBound.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_DFTSampleBound

/-!
# The Information-Theoretic DFT Sample Bound: `K ≥ r`

Shor's algorithm extracts the period `r` of `x ↦ a^x mod N` from the discrete
Fourier transform of a period-`r` signal.  A recurring hope for "classical
Shor" is that *few* Fourier samples might suffice.  This file proves that this
is impossible, in the strongest (representation-independent) form:

* `exists_indistinguishable_of_finrank_lt` — a linear measurement scheme with
  fewer measurements than the dimension of the signal space always confuses two
  distinct signals;
* `dft_lt_period_indistinguishable` — concretely: for `K < r` and *any* choice
  of `K` frequencies, two distinct period-`r` signals have identical DFT samples
  at those frequencies;
* `dft_sample_count_ge_period` — hence any family of sample frequencies that
  determines the signal must have `K ≥ r`.  This is the advertised bound.
* `dft_full_samples_determine` — sharpness: `r` samples (all frequencies) do
  determine the signal, since `ZMod.dft` is a linear equivalence.

The bound is unconditional and information-theoretic: it does not depend on the
computational model, only on `ℂ`-linearity of Fourier sampling.
-/

open FactoringBarriers

open Module

/-! ## The abstract dimension bound -/

/-- **Dimension bound on linear measurement.** A `ℂ`-linear measurement map into
a space of strictly smaller finite dimension cannot separate all signals. -/
theorem exists_indistinguishable_of_finrank_lt
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (M : V →ₗ[ℂ] W) (h : finrank ℂ W < finrank ℂ V) :
    ∃ v w : V, v ≠ w ∧ M v = M w := by
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective M := by
    intro a b hab
    by_contra hne
    exact hne (by simpa using (hcon a b hne hab).elim)
  exact absurd (LinearMap.finrank_le_finrank_of_injective hinj) (by omega)

/-! ## Fourier sampling on `ZMod r` -/

variable {r K : ℕ} [NeZero r]



theorem finrank_signal_space : finrank ℂ (ZMod r → ℂ) = r := by
  simp [ZMod.card]

theorem finrank_sample_space : finrank ℂ (Fin K → ℂ) = K := by
  simp

/-- **Fewer than `r` Fourier samples are blind.** For any choice of `K < r`
sample frequencies there are two *distinct* signals on `ZMod r` whose discrete
Fourier transforms agree at every sampled frequency. -/
theorem dft_lt_period_indistinguishable (hK : K < r) (idx : Fin K → ZMod r) :
    ∃ v w : ZMod r → ℂ, v ≠ w ∧ ∀ j : Fin K, ZMod.dft v (idx j) = ZMod.dft w (idx j) := by
  obtain ⟨v, w, hvw, h⟩ :=
    exists_indistinguishable_of_finrank_lt (dftSample idx)
      (by rw [finrank_signal_space, finrank_sample_space]; exact hK)
  exact ⟨v, w, hvw, fun j => congrFun h j⟩





open FactoringBarriers in
theorem solution(idx : Fin K → ZMod r)
    (hdet : ∀ v w : ZMod r → ℂ, (∀ j : Fin K, ZMod.dft v (idx j) = ZMod.dft w (idx j)) → v = w) :
    r ≤ K := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨v, w, hvw, h⟩ := dft_lt_period_indistinguishable hlt idx
  exact hvw (hdet v w h)
