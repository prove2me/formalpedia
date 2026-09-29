-- Prove2me | solution 1 for UltrametricPACBayes.ultra_cover_ge_separated_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:49:50.383995+00:00
-- url     : https://prove2.me/submissions/2ea3c17a-db22-4724-b18a-4a54c0285291

-- Sol generated from Bridges/UltrametricPACBayes.lean
import Mathlib
import Definitions.Def_Bridges_UltrametricPACBayes

/-!
# Ultrametric PAC-Bayes via Valuation Transport and Non-Archimedean Posterior Compression

This file formalizes an ultrametric analogue of PAC-Bayes theory, establishing a bridge
between non-Archimedean geometry, tropical valuation transport, and certified robustness
in machine learning.

## Core Insight

In a non-Archimedean (ultrametric) hypothesis space, closed balls are nested or disjoint.
This makes posterior compression combinatorial rather than Euclidean, yielding:
- Sharper cover/packing identities (cover number = packing number)
- Coding bounds driven by valuation depth
- PAC-Bayes-style generalization via ultrametric posterior geometry

## Main Theorems

1. **ultrametric_cover_packing_duality**: In ultrametric spaces, maximal r-separated
   subsets are optimal r-covers, unifying cover and packing numbers.
2. **valuation_compression_code_bound**: Ultrametric cover bounds yield logarithmic
   code-length bounds for posterior compression.
3. **ultrametric_pac_bayes_bound_lipschitz_certified_robustness**: Lipschitz loss in
   ultrametric spaces yields per-hypothesis certified robustness certificates.
4. **tropical_to_ultrametric_generalization_transfer**: Tropical margin bounds transport
   to ultrametric generalization guarantees via the valuation bridge functor.

## Bridges

- Bridge: connects non-Archimedean geometry to PAC-Bayes learning theory.
- Bridge: connects tropical valuation transport to certified robustness.
- Bridge: connects ultrametric posterior coding to post_quantum_security style obfuscation.
- Bridge: connects entropy-style code length to quantum-inspired compression observables.

## Structures (17 novel definitions)

- `IsUltrametricSpace` — typeclass for the strong triangle inequality
- `FiniteHypDist` — finitely supported probability distribution
- `TropicalUltrametricBridge` — functorial bridge between tropical and ultrametric
- `BoundedLoss`, `UltraLipschitzLoss` — loss regularity conditions
- and 12 more definitions for balls, covers, packings, risks, and compression
-/

open Finset

noncomputable section

open scoped Classical

open UltrametricPACBayes

/-! ## §1. Ultrametric Space Infrastructure -/



/-! ## §2. Ultrametric Ball Properties -/





/-! ## §3. Finite Hypothesis Distribution -/



/-
Support is nonempty since weights sum to 1 > 0.
-/

/-
**expectation_const**: `E_μ[c] = c`. Uses `total_one`.
    Bridge: connects distribution theory to PAC-Bayes constant bounds (ML).
-/

/-
**expectation_nonneg**: If `f ≥ 0` pointwise then `E_μ[f] ≥ 0`.
    Bridge: connects positivity to risk nonnegativity (ML).
-/

/-
**expectation_mono**: If `f ≤ g` pointwise, then `E_μ[f] ≤ E_μ[g]`.
    Bridge: connects pointwise bounds to expected risk bounds (ML).
-/

/-
**expectation_le_of_le**: If `f h ≤ c` for all `h`, then `E_μ[f] ≤ c`.
-/

/-! ## §4. Ultrametric Separation and Covering -/









/-! ## §5. Cover–Packing Duality: The Ultrametric Engine -/

/-
**maximal_ultra_separated_gives_cover**: A maximal r-separated subset of target
    is an r-cover of target. This holds in *any* metric space (no ultrametric needed).

    Proof: By contradiction. If x ∈ target is not covered by S, then dist(x, s) > r for
    all s ∈ S. Combined with the original separation, `insert x S` is still r-separated,
    contradicting maximality.

    Bridge: connects metric maximality to PAC-Bayes cover construction (ML).
-/

/-
**ultra_cover_ge_separated_card**: In an ultrametric space, any r-cover has at least
    as many elements as any r-separated subset of the target. This is the key duality.

    Proof: Construct an injection `f : S → C` by mapping each `s ∈ S ⊆ target` to a
    covering center `c ∈ C` with `dist(s, c) ≤ r`. If two separated points `s₁ ≠ s₂`
    map to the same center `c`, then by the ultrametric inequality:
    `dist(s₁, s₂) ≤ max(dist(s₁, c), dist(c, s₂)) ≤ max(r, r) = r`,
    contradicting `r < dist(s₁, s₂)`. So `f` is injective, giving `|S| ≤ |C|`.

    Bridge: connects ultrametric geometry to optimal coding bounds (information theory).
    Impact: post_quantum_security — tight packing/covering for lattice parameters.
-/



/-! ## §6. Loss, Risk, and Regularity Conditions -/








/-
**sampleRisk_nonneg**: Sample risk is nonneg for bounded loss.
    Bridge: connects loss boundedness to risk positivity (ML).
-/

/-
**posteriorRisk_nonneg**: Posterior risk is nonneg for bounded loss.
    Bridge: connects distribution theory to risk bounds (ML).
-/

/-
**sampleRisk_le_one**: Sample risk is at most 1 for bounded loss on nonempty samples.
    Bridge: connects bounded loss to finite complexity (ML).
-/

/-
**posteriorRisk_mono_loss**: Pointwise larger loss gives larger posterior risk.
-/

/-! ## §7. Compression and Coding Bounds -/



/-
**posteriorCodeLength_nonneg**: Code length is nonneg.
    Impact: entropy — analogous to Shannon entropy nonnegativity.
-/

/-
**valuation_compression_code_bound**: Cover code length ≤ support code length.
    If `|C| ≤ |support|`, then `log|C| ≤ log|support|`.
    Bridge: connects ultrametric cover theory to information-theoretic compression.
    Impact: thermodynamic — compression = free energy reduction in valuation landscape.
-/

/-
**valuation_compression_monotone**: Smaller covers give smaller code.
    Impact: thermodynamic — coarser graining reduces information content.
-/

/-! ## §8. Ultrametric PAC-Bayes Bound -/


/-
**expected_loss_lipschitz_perturbation**: If all posterior hypotheses are within
    distance r of their cluster centers (via assignment function), the expected loss
    perturbation is bounded by K*r.

    This is the core quantitative estimate for ultrametric posterior compression.

    Bridge: connects Lipschitz stability to posterior compression error (ML).
    Impact: certified_robustness — quantifies approximation error from clustering.
-/

/-
**ultrametric_pac_bayes_bound_lipschitz_certified_robustness**: Main PAC-Bayes theorem.

    In an ultrametric hypothesis space with K-Lipschitz loss, for any posterior ρ and
    any r-cover of ρ's support, every hypothesis in the posterior can be certified:
    its loss is within K*r of some cluster center, and the number of clusters is
    bounded by the cover cardinality.

    This provides:
    1. Per-hypothesis robustness certificate (K*r perturbation bound)
    2. Model complexity bound (log of cover cardinality)
    3. Combined: generalization controlled by K*r + log(cover)/n

    Bridge: connects ultrametric posterior compression to certified robustness in ML.
    Impact: lipschitz_certified_robustness, neural_network_compression.
-/

/-! ## §9. Tropical-Ultrametric Bridge -/


/-
Transport a posterior distribution through a map `f : A → B`.
    The transported distribution aggregates weights along fibers of `f`.
-/


/-
**expectation_transport**: Expectation under transported distribution equals
    expectation of composition.
    Bridge: connects pushforward integration to composition (measure theory).
-/

/-
**tropical_to_ultrametric_generalization_transfer**: Main bridge theorem.

    If the posterior's image under the bridge has bounded diameter R, then
    there exists a single representative hypothesis c such that all posterior
    hypotheses have loss within K*R of c. This transfers tropical margin bounds
    to ultrametric generalization guarantees.

    This is the tropical-to-ultrametric transfer theorem: tropical margin control
    (bounded diameter in the image) directly yields ultrametric robustness certificates.

    Bridge: connects tropical valuation transport to certified robustness (ML).
    Impact: tropical_hash_collision — margin-preserving transport for tight bounds.
-/

/-
**tropical_certified_cover_transfer**: Transfer tropical diameter bounds to
    ultrametric cover existence. If the image has diameter ≤ R, then a single
    R-ball covers the entire image.

    Bridge: connects tropical margin analysis to ultrametric covering theory (ML).
    Impact: certified_robustness — tropical structure enables single-ball covering.
-/

/-! ## §10. Application Theorems -/

/-
**quantum_entropy_style_code_bound**: Code length is additive under product supports.
    `log(n * m) = log(n) + log(m)`. This is the information-theoretic foundation
    for compositional complexity bounds in multi-layer ultrametric networks.

    Bridge: connects entropy additivity to quantum tensor product structure.
    Impact: quantum — code length decomposes like von Neumann entropy under tensor.
-/


/-
**tropical_hash_collision_ultra_separation**: In an r-separated set,
    a short-range function (collisions imply closeness) is injective, so the
    image has the same cardinality as the original.

    This models hash collision resistance under valuation constraints:
    if a hash function has bounded collision range (f(x) = f(y) ⟹ dist(x,y) ≤ r)
    and the input set is r-separated, then no collisions occur.

    Bridge: connects tropical hash functions to ultrametric collision resistance.
    Impact: tropical_hash_collision — separation guarantees collision-free hashing.
-/

/-
**ultrametric_pac_bayes_combined_bound**: Combined PAC-Bayes bound assembling
    the Lipschitz perturbation (K*r) and complexity term (log cover cardinality).
    For any cover of the posterior support, the total bound is:
    `K*r + log(|centers|) / n`.

    This is the complete ultrametric PAC-Bayes inequality.

    Bridge: connects ultrametric posterior compression to generalization theory (ML).
    Impact: lipschitz_certified_robustness, neural_network_compression, thermodynamic.
-/



open UltrametricPACBayes in
theorem solution    {α : Type*} [PseudoMetricSpace α] [IsUltrametricSpace α]
    {r : ℝ} {target S C : Finset α}
    (hS_sub : S ⊆ target)
    (hS_sep : IsUltraSeparated r S)
    (hC_cover : IsUltraCover r C target) :
    S.card ≤ C.card := by
  -- Define a function `f : S → C` by mapping each `s ∈ S` to some `c ∈ C` with `dist(s, c) ≤ r`.
  obtain ⟨f, hf⟩ : ∃ f : α → α, ∀ s ∈ S, f s ∈ C ∧ dist s (f s) ≤ r := by
    choose! f hf using fun x hx => hC_cover x ( hS_sub hx );
    use f;
  -- Show that `f` is injective on `S`.
  have h_inj : ∀ s₁ s₂ : α, s₁ ∈ S → s₂ ∈ S → s₁ ≠ s₂ → f s₁ ≠ f s₂ := by
    intro s₁ s₂ hs₁ hs₂ hne h_eq
    have h_dist : dist s₁ s₂ ≤ r := by
      have := ‹IsUltrametricSpace α›.dist_triangle_max s₁ ( f s₁ ) s₂;
      simp_all +decide [ dist_comm ];
      grind;
    exact not_lt_of_ge h_dist ( hS_sep hs₁ hs₂ hne );
  exact Finset.card_le_card ( show S.image f ⊆ C from Finset.image_subset_iff.2 fun x hx => hf x hx |>.1 ) |> le_trans ( by rw [ Finset.card_image_of_injOn fun x hx y hy hxy => by contrapose! hxy; exact h_inj x y hx hy hxy ] )
