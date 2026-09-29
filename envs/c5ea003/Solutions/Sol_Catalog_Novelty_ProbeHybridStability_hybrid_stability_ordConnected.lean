-- Prove2me | solution 1 for Catalog.Novelty.ProbeHybridStability.hybrid_stability_ordConnected
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:14:10.418048+00:00
-- url     : https://prove2.me/submissions/32b9379e-a7ec-4128-9609-fe9a5e0a4109

-- Sol generated from Novelty/ProbeHybridStability.lean
import Mathlib
import Definitions.Def_Novelty_ProbeHybridStability
import Definitions.Def_Novelty_ProbeRetentionLimits
import Theorems.Thm_Catalog_Novelty_ProbeHybridStability_isTopSet_hybrid_iff

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






omit [Fintype ι] in
/-- **The stability region is convex.**  If a selection survives the mixture at
two weights it survives at every weight in between.  Consequently a domain in
which the mixture harms can only harm *monotonically*: leaving the stability
interval is irreversible in `λ`. -/
theorem hybrid_stability_convex {h p : ι → ℝ} {B : ℕ} {S : Finset ι} {lam₁ lam₂ t : ℝ}
    (h1 : IsTopSet (hybrid h p lam₁) B S) (h2 : IsTopSet (hybrid h p lam₂) B S)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsTopSet (hybrid h p ((1 - t) * lam₁ + t * lam₂)) B S := by
  obtain ⟨hcard, hA⟩ := isTopSet_hybrid_iff.mp h1
  obtain ⟨-, hB⟩ := isTopSet_hybrid_iff.mp h2
  refine isTopSet_hybrid_iff.mpr ⟨hcard, fun i hi j hj => ?_⟩
  have hA' := hA i hi j hj
  have hB' := hB i hi j hj
  have e1 : (1 - t) * (lam₁ * (p j - p i)) ≤ (1 - t) * (h i - h j) :=
    mul_le_mul_of_nonneg_left hA' (by linarith)
  have e2 : t * (lam₂ * (p j - p i)) ≤ t * (h i - h j) :=
    mul_le_mul_of_nonneg_left hB' ht0
  nlinarith [e1, e2]


/-! ### 3. Two explicit four-key instances -/



















/-! ### 4. The `L∞` transfer constant cannot be improved -/






open Catalog.Novelty.ProbeHybridStability in
omit [Fintype ι] in
theorem solution{h p : ι → ℝ} {B : ℕ} {S : Finset ι}
    {lam₁ lam₂ lam : ℝ} (h1 : IsTopSet (hybrid h p lam₁) B S)
    (h2 : IsTopSet (hybrid h p lam₂) B S) (hlt : lam₁ ≤ lam) (hgt : lam ≤ lam₂) :
    IsTopSet (hybrid h p lam) B S := by
  rcases eq_or_lt_of_le (hlt.trans hgt) with heq | hlt'
  · have : lam = lam₁ := le_antisymm (heq ▸ hgt) hlt
    exact this ▸ h1
  · have ht0 : 0 ≤ (lam - lam₁) / (lam₂ - lam₁) := by
      apply div_nonneg <;> linarith
    have ht1 : (lam - lam₁) / (lam₂ - lam₁) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have := hybrid_stability_convex h1 h2 ht0 ht1
    have hne : lam₂ - lam₁ ≠ 0 := ne_of_gt (by linarith)
    have heq2 : (1 - (lam - lam₁) / (lam₂ - lam₁)) * lam₁
        + (lam - lam₁) / (lam₂ - lam₁) * lam₂ = lam := by
      have hrw : (1 - (lam - lam₁) / (lam₂ - lam₁)) * lam₁
          + (lam - lam₁) / (lam₂ - lam₁) * lam₂
          = lam₁ + ((lam - lam₁) / (lam₂ - lam₁)) * (lam₂ - lam₁) := by ring
      rw [hrw, div_mul_cancel₀ _ hne]
      ring
    rwa [heq2] at this
