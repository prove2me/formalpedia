-- Prove2me | solution 1 for Catalog.Novelty.ProbeHybridStability.accuracy_does_not_order_retention
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:12:20.029826+00:00
-- url     : https://prove2.me/submissions/f3b2cad8-c769-4521-9e94-a3a6763d46e8

-- Sol generated from Novelty/ProbeHybridStability.lean
import Mathlib
import Definitions.Def_Novelty_ProbeHybridStability
import Definitions.Def_Novelty_ProbeRetentionLimits
import Theorems.Thm_Catalog_Novelty_ProbeRetentionLimits_eq_of_isTopSet_of_strict

/-!
# Why the hybrid arm cannot hurt, and when it helps (NET-69, interaction layer)

`Novelty.ProbeRetentionLimits` analysed a *single* score.  NET-69's third arm
mixes two: the accumulated heavy-hitter statistic `h` and the content probe `p`
are combined into `hybrid h p λ = h + λ · p`, and the measurement is that on
code the mixture is **non-degrading** (`0.9371` versus `0.9340` for `λ = 1`),
whereas on prose the same mixture harms monotonically.  This file explains that
asymmetry structurally.

* `isTopSet_hybrid_iff` — the selection `S` survives the mixture iff a *linear*
  system in `λ` holds, one inequality per retained/discarded pair.
* `hybrid_isTopSet_of_margin` — hence an explicit **non-degradation threshold**:
  if the accumulated score separates `S` from its complement by a margin `γ` and
  the probe has oscillation at most `D`, then every `λ ≤ γ/D` leaves the
  selection, and therefore the retained mass, untouched.  Non-degradation is a
  margin phenomenon, not a property of the probe's accuracy.
* `hybrid_stability_convex` and `hybrid_stability_ordConnected` — the set of
  mixing weights that preserve a given selection is an **interval** containing
  every weight between any two of its members.  This is the structural reason a
  domain can only exhibit *monotone* harm: once `λ` leaves the stability
  interval of the accumulated selection it never re-enters it.
(The uniqueness lemma `eq_of_isTopSet_of_strict` of `Novelty.ProbeRetentionLimits`
makes the numerical instances below unambiguous.)

Section 3 contains two fully explicit four-key instances, both verified
numerically before being formalised (see `ComputationalEvidence.md`).

* `accuracy_does_not_order_retention` — a score that is **four times more
  accurate** in `L²` (`SSE = 150` versus `1802`) retains **nineteen times less**
  mass (`1` versus `19`).  Prediction accuracy does not order retention even
  weakly; this is the counterexample that blocks the naive reading "the probe
  arm loses because its `R²` is low", and it is the exact companion of
  `exists_probe_perfect_retention_with_Rsq`.
* `hybrid_strictly_beats_both_arms` — an instance in the NET-69 régime where the
  accumulated arm retains `11`, the probe-only arm `9`, and the `λ = 1` hybrid
  `19`: strictly more than either parent.  So the measured `+0.3` points are not
  noise-shaped luck; a mixture can strictly dominate both arms because the two
  scores misrank *different* pairs.
* `hybrid_stability_threshold_example` — for that instance the stability
  interval of the accumulated selection is exactly `[0, 2/5]`, and the mixture
  helps precisely because `λ = 1` lies outside it.  Deployment corollary:
  choosing `λ` below the margin ratio guarantees safety but also guarantees the
  hybrid learns nothing from the probe.

Section 4 closes the loop on the *pessimism* of the transfer theorems:

* `sup_transfer_bound_is_sharp` — a four-key instance attaining the constant
  `2Bε` of `retained_ge_of_isTopSet_sup` exactly.  The bound cannot be improved,
  so the gulf between it and the `R²`-perfect probe of
  `exists_probe_perfect_retention_with_Rsq` is real: `L∞`/`L²` accuracy pins
  down retention only up to the full worst case.
-/

open Catalog.Novelty.ProbeHybridStability

open Finset Catalog.Novelty.ProbeRetentionLimits

variable {ι : Type*} [Fintype ι]

/-! ### 1. The mixture and its stability interval -/








/-! ### 3. Two explicit four-key instances -/





lemma sse_hBad : sse aEx hBad = 150 := by
  simp [sse, aEx, hBad, Fin.sum_univ_four]
  norm_num

lemma sse_pGood : sse aEx pGood = 1802 := by
  simp [sse, aEx, pGood, Fin.sum_univ_four]
  norm_num













/-! ### 4. The `L∞` transfer constant cannot be improved -/






open Catalog.Novelty.ProbeHybridStability in
theorem solution:
    sse aEx hBad < sse aEx pGood ∧
      (∀ S, IsTopSet hBad 2 S → retained aEx S = 1) ∧
      (∀ T, IsTopSet pGood 2 T → retained aEx T = 19) := by
  refine ⟨by rw [sse_hBad, sse_pGood]; norm_num, ?_, ?_⟩
  · intro S hS
    have hSeq : S = ({2, 3} : Finset (Fin 4)) := by
      refine eq_of_isTopSet_of_strict (B := 2) (by decide) ?_ hS
      intro i hi j hj
      fin_cases i <;> fin_cases j <;> simp_all [hBad] <;> norm_num
    subst hSeq
    rw [retained, Finset.sum_pair (show (2 : Fin 4) ≠ 3 by decide)]
    norm_num [aEx, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  · intro T hT
    have : T = ({0, 1} : Finset (Fin 4)) := by
      refine eq_of_isTopSet_of_strict (B := 2) (by decide) ?_ hT
      intro i hi j hj
      fin_cases i <;> fin_cases j <;> simp_all [pGood] <;> norm_num
    subst this
    norm_num [retained, aEx]
