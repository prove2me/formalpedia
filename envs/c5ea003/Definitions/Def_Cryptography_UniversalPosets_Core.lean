-- Prove2me | Definitions.Def_Cryptography_UniversalPosets_Core
-- name    : Cryptography_UniversalPosets_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:25:19.814511+00:00
-- url     : https://prove2.me/theorems/8fe28e7e-2f1a-4b3c-a35e-9c372674e1a1
-- title:
--   Aether Catalog definitions — Cryptography_UniversalPosets_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.UniversalPosets.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/UniversalPosets/Core.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BiOrderSeparation

/-!
# Transitivity-preserving Boolean labels for finite posets

A point of a poset is labeled by its principal ideal.  Inclusion between labels is
then equivalent, not merely implied, by the original order.  Thus the Boolean
lattice on the ground set is an induced universal host for every order on that
set.  This is the canonical uncompressed labeling that motivates smaller
transitivity-preserving schemes.

The development also records functoriality, a meet-semilattice compatibility
law, a cardinality lower bound for every induced universal host, and a bridge
to collision-resistant bounded word traces.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): six falsifiable targets were ranked by impact: (1) every
finite poset admits an induced Boolean labeling by principal ideals; (2) such
labels compose through any induced host embedding; (3) meet structure is carried
to intersection; (4) every universal host has at least as many points as each
poset it hosts; (5) the Boolean host has exactly exponential cardinality; and
(6) collision-resistant word traces determine the corresponding order labels.
The bold continuation targets are subexponential coordinate compression,
regularity-based block labels, and entropy-optimal separating families.

Experiment (Experimenter): principal ideals were tested against equality,
comparability, and incomparability.  The witness `x` itself reflects inclusion:
if the label of `x` is included in the label of `y`, reflexivity puts `x` in its
own label and hence gives `x ≤ y`.  Intersections were tested in a meet
semilattice and agree exactly with the label of the meet.

Analysis (Analyst): transitivity needs no separate closure operation because it
is inherited from subset inclusion.  The construction uses one Boolean
coordinate per source point, explaining the baseline host size `2^n`.  Any
improvement must compress coordinates while retaining enough witnesses to
reflect every failed comparison.

Critique (Critic): this file does not claim the asymptotically sharper host bound
from the motivating paper; that bound requires substantial regularity and
counting infrastructure.  The results here are exact and non-vacuous, but the
canonical host is exponentially larger than the paper's host.  Edge cases,
including empty and singleton types, are covered.  No claim relies only on a
cardinality computation.

Synthesis (Principal Investigator): the induced-label theorem, composition law,
meet law, cardinal lower bound, exact Boolean-host size, and trace-rigidity bridge form
a reusable foundation for studying compressed universal-poset labels.
-/

open Set
open scoped Classical

namespace UniversalPosets

/-- A map is an induced embedding when it is injective and preserves and reflects order. -/
def IsInducedOrderEmbedding {P U : Type*} [LE P] [LE U] (f : P → U) : Prop :=
  Function.Injective f ∧ ∀ x y, f x ≤ f y ↔ x ≤ y

/-- The principal-ideal Boolean label of a point. -/
def principalLabel {P : Type*} [LE P] (x : P) : Set P :=
  {y | y ≤ x}










end UniversalPosets


