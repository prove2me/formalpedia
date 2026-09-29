-- Prove2me | Theorems.Thm_UniversalPosets_bipRel_isPartialOrder
-- name    : UniversalPosets.bipRel_isPartialOrder
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:04:20.891512+00:00
-- url     : https://prove2.me/theorems/2cff8af2-a757-4644-a554-4a5a14060b2e
-- title:
--   `bipRel R` really is a partial order (height at most two, hence transitive).
-- statement:
--   `bipRel R` really is a partial order (height at most two, hence transitive).
--
--   ```lean
--   theorem UniversalPosets.bipRel_isPartialOrder(R : Fin k → Fin l → Prop) :
--       IsPartialOrder (Fin k ⊕ Fin l) (bipRel R) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/UniversalPosets/Bounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/UniversalPosets/Bounds.lean#L132

-- Thm stub generated from Cryptography/UniversalPosets/Bounds.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_Bounds
import Definitions.Def_Cryptography_UniversalPosets_Core

/-!
# Quantitative bounds for universal posets

This file complements `Cryptography.UniversalPosets.Core` with *quantitative*
information about universal hosts: how many points a poset must have in order to
contain a whole class of `n`-element posets as induced subposets.

The motivating paper ("Even smaller universal posets") produces, for every
`η > 0` and large `n`, a host of size `2^{(1+η)n/2}` containing every `n`-element
poset as an induced subposet.  Two features of that statement are made precise
and proved here:

* the **counting lower bound**: any host that already contains all *bipartite*
  (height `≤ 2`) posets with parts of sizes `k` and `l` must satisfy
  `2 ^ (k*l) ≤ N ^ (k+l)`, i.e. `log₂ N ≥ kl/(k+l)`.  With `k = l = n/2` this is
  the classical `N ≥ 2^{n/4}` bound, the best lower bound currently known;
* the **balanced bipartite upper bound**: an explicit host of size
  `k + 2^k * l` which contains *every* `(k,l)`-bipartite poset as an induced
  subposet.  With `k = l = n/2` its size is `(n/2)(2^{n/2} + 1)`, matching the
  exponent `n/2` of the paper on the extremal subclass.

Together these give, for the balanced bipartite class on `n = 2m` points,
`2^{m/2} ≤ U(m,m) ≤ m·2^m + m`, i.e. the optimal exponent lies between `n/4`
and `n/2 + o(n)`; the paper's theorem says the exponent for the *full* class of
`n`-element posets is at most `(1+η)n/2`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer). Seven falsifiable targets were ranked:
(1) the Boolean lattice on the ground set is universal for *all* orders on that
set, not only for a fixed one (generalising `Core`);
(2) universality is a *relation*-level statement, so it survives passing to the
bipartite subclass;
(3) counting bipartite orders forces `2^{kl} ≤ N^{k+l}` for every host;
(4) hence `N ≥ 2^{kl/(k+l)}` after an analytic (rpow) interpolation step;
(5) an explicit "index-tagged neighbourhood" host of size `k + l·2^k` is
universal for the `(k,l)`-bipartite class -- so the exponent `n/2` is attained
on the class where the counting bound is tight up to a factor 2;
(6) for `k = l = 1` the truth is exactly `3`, so the crude counting bound
(`N ≥ 2`) is *not* tight;
(7) duplicate elements force the tag coordinate: neighbourhood labels alone are
not injective.

Experiment (Experimenter). (1)-(6) were formalised and proved.  Target (7)
appears as `bipHost_tag_needed`: the two elements of the second part of a
`(k,2)`-bipartite poset with equal down-sets receive different host points, so
the `Fin l` tag cannot be dropped.  The `k = l = 1` case was computed by hand
and confirms `U = 3 = 1 + 2^1·1`, exactly the size of the explicit host.

Analysis (Analyst). The gap between `2^{n/4}` and `2^{n/2}` is *not* a defect of
the counting method applied to a poor class: on the balanced bipartite class the
number of orders is `2^{n²/4}` while a host of size `2^{n/2}` has roughly
`2^{n²/4}` induced sub-configurations too, so the counting bound loses exactly a
factor `2` in the exponent because a host point may be reused by many different
embeddings.  Removing that factor is precisely what the regularity-based
argument of the paper does; it is out of scope of a self-contained file, and no
`sorry` is used to pretend otherwise.

Critique (Critic). Every statement below is about explicitly constructed
objects; nothing is vacuous: the hypotheses `IsBipartiteUniversal` are witnessed
by `bipHost_isBipartiteUniversal`, and the small case `k = l = 1` is decided in
both directions.  No `native_decide`, no `sorry`.
-/

open Function

open UniversalPosets

variable {k l : ℕ}

/-! ## Universality -/




/-! ## The Boolean host: the naive `2^n` upper bound -/



/-! ## Bipartite (height ≤ 2) orders -/

theorem UniversalPosets.bipRel_isPartialOrder(R : Fin k → Fin l → Prop) :
    IsPartialOrder (Fin k ⊕ Fin l) (bipRel R) := by sorry
