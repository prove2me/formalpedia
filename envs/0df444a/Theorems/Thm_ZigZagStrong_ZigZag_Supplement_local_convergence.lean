-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_Supplement_local_convergence
-- name    : ZigZagStrong.ZigZag.Supplement.local_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:03.587627+00:00
-- url     : https://prove2.me/theorems/e94862ff-e5ae-476d-858b-693db7938196
-- title:
--   Lemma 4.2 — local convergence of configuration multigraphs to $T_D$
-- statement:
--   Let $d(n)$ be degree sequences satisfying the standing assumptions of §4 with limiting degree law $D$, and let $G_n$ be the configuration multigraph of a uniformly random pairing of the half-edges of $d(n)$. Fix a radius $R$ and a finite rooted multigraph $H$ (unrelated to the zig-zag gadget). Then
--   $$\frac{\#\{v\in[n]: B_R^{G_n}(v)\cong H\}}{n}\ \xrightarrow{\ P\ }\ P\big(B_R^{T_D}(r)\cong H\big),$$
--   where $B_R$ denotes the radius-$R$ neighbourhood (the induced sub-multigraph on the vertices at distance at most $R$), rooted at its centre, and $\cong$ is rooted isomorphism.
--
--   This is the input from which the limiting spectral law of Proposition 4.3 is derived.
--
--   Differences from the source:
--   - reading: a finite rooted graph H → any finite rooted multigraph K (adjacency counts, a loop counted twice), compared by rooted multigraph isomorphism; reason: the neighbourhoods of G_n are multigraphs (loops and multiple edges are retained, p. 16); for a simple rooted graph H this is the source statement verbatim
--   - encoding: the standing assumptions of §4 (positive degrees, even total degree, uniform bound Δ, empirical degree distribution converging in distribution to D, δ ≥ 2 throughout) → the Prop-structure DegreeRegime deg D, with convergence in distribution written as pointwise convergence of the empirical degree frequencies to D(k); reason: for laws on the nonnegative integers convergence in distribution is equivalent to pointwise convergence of the probability mass functions; each field is one assumption of pp. 15–16
--   - encoding: a uniformly random perfect matching of the N labelled half-edges; loops and multiple edges retained → the uniform law on fixed-point-free involutions of the half-edge type Σ i, Fin (d_i); adjacency A(i,j) counts half-edges of i paired into j, so a loop adds 2 to the diagonal; reason: a perfect matching of a finite set is the same thing as a fixed-point-free involution; the count gives exactly the source adjacency with row sums d_i
--   - encoding: the unimodular Galton–Watson tree T_D (root with D children, every other vertex D* − 1 children, independently) → Ulam–Harris coding: an independent product law (Measure.infinitePi) on child counts c : List ℕ → ℕ, D at the root address [] and D* − 1 at every other address; vertices are the addresses whose indices are below the parent counts; reason: the standard construction of a Galton–Watson tree; the law of the tree and of every finite neighbourhood is the source one
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Lemma 4.2, p. 17.

import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_ZigZagStrong_ZigZag_Supplement_GaltonWatson

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag.Supplement
open Filter MeasureTheory
open scoped BigOperators Topology

theorem local_convergence (deg : ∀ n : ℕ, Fin n → ℕ) (D : PMF ℕ) (hreg : DegreeRegime deg D)
    (R : ℕ) (K : RootedMultigraph) [Finite K.V] :
    ProbConverges (fun n => finiteLaw (Ω := Pairing (HalfEdge (deg n))))
      (fun n τ => (Nat.card {v : Fin n // RootedIso (nbhd (configAdj τ) v R) K} : ℝ) / (n : ℝ))
      ((gwLaw D).real {c | RootedIso (treeNbhd c R) K}) := by sorry

end ZigZagStrong.ZigZag.Supplement
