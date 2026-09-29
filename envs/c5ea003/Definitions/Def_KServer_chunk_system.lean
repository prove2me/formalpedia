-- Prove2me | Definitions.Def_KServer_chunk_system
-- name    : KServer_chunk_system
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T09:37:31.690854+00:00
-- url     : https://prove2.me/theorems/3586e194-f86e-4f5d-88b0-e0600699d1c5
-- title:
--   Chunk systems: the BCR Lemma 6 induction package
-- statement:
--   A **chunk system** on a metric space $X$ with marked points $s, t$ packages the induction hypothesis of Bubeck–Coester–Rabani's Lemma 6 (STOC 2023): a finitely supported random sequence of $m$ chunks $\rho_1, \dots, \rho_m$ of set requests, with adapted sizes $c_1, \dots, c_m$, such that
--
--   1. every requested set is nonempty, the last request is $\{t\}$, and the optimal offline evader cost of the whole sequence from $s$ is at most $d(s,t)$;
--   2. $c_i$ is a function of the first $i-1$ chunks (`hmeas`);
--   3. **conditional cost bound**: for every deterministic evader algorithm and every value of the past, the conditional expected cost of serving chunk $i$ — even with an escape price of `price` available on it — is at least $c_i$ (`hcost`, stated multiplicatively over the atoms of the past, so empty atoms are harmless);
--   4. $c_i \in [c_{\mathrm{Lo}}, c_{\mathrm{Hi}}]$, the expected total size is at least `total`, and $m \ge m_{\mathrm{Lo}}$.
--
--   BCR's Lemma 6 for their space $\mathcal{M}_w$ is the existence of a chunk system with $c_{\mathrm{Lo}} = D/2\beta$, $c_{\mathrm{Hi}} = 3D/2\beta$, `total` $= \alpha w^2 D$, `price` $= 2D$ and $m_{\mathrm{Lo}} = \lceil \alpha\beta w^2 \rceil$, where $D = d(s,t)$.
--
--   Also included: `pathMetric β`, the base-case space of $\beta + 1$ equally spaced points on a line (`Fin (β+1)` with the metric induced from ℝ).
--
--   ## Formalization note
--
--   Randomness is a finite weighted sample space; conditioning is on the tuple of past chunks. The escape-price cost is the `escapeCost` of the evader definitions — the minimum over bail-out times, which dominates every online escape strategy.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 6.

import Mathlib
import Definitions.Def_KServer_evader

namespace KServer

/-- The path space: `β + 1` equally spaced points on a line, the base case of the
Bubeck–Coester–Rabani construction. -/
@[reducible] noncomputable def pathMetric (β : ℕ) : MetricSpace (Fin (β + 1)) :=
  MetricSpace.induced (fun i => (i : ℝ)) (fun i j h => by
    exact_mod_cast Fin.ext (Nat.cast_injective h)) inferInstance

/-- A **chunk system** on a metric space with marked points `s, t`: a finitely
supported random sequence of `m` chunks of set requests together with adapted
sizes, as in BCR's Lemma 6. The numeric parameters: sizes lie in `[cLo, cHi]`,
the expected total size is at least `total`, and the conditional cost lower
bound holds against every evader even with an escape price of `price` on the
current chunk. -/
structure ChunkSystem (X : Type*) [MetricSpace X] (s t : X)
    (cLo cHi total price : ℝ) (mLo : ℕ) where
  /-- the finite sample space -/
  Ω : Type
  [instFin : Fintype Ω]
  [instDec : DecidableEq Ω]
  /-- outcome weights -/
  P : Ω → ℝ
  /-- the number of chunks -/
  m : ℕ
  /-- the chunks -/
  chunk : Ω → Fin m → List (Set X)
  /-- the sizes -/
  size : Ω → Fin m → ℝ
  hP : ∀ ω, 0 ≤ P ω
  hPsum : ∑ ω, P ω = 1
  hm : mLo ≤ m
  hm0 : 0 < m
  hne : ∀ ω i, ∀ S ∈ chunk ω i, S.Nonempty
  hlast : ∀ ω, (((List.ofFn (chunk ω)).flatten).getLast?) = some {t}
  hopt : ∀ ω, evaderOfflineCost s ((List.ofFn (chunk ω)).flatten) ≤ dist s t
  hsize : ∀ ω i, cLo ≤ size ω i ∧ size ω i ≤ cHi
  hmeas : ∀ (i : Fin m) (ω ω' : Ω),
    ((List.ofFn (chunk ω)).take i = (List.ofFn (chunk ω')).take i) → size ω i = size ω' i
  hcost : ∀ (i : Fin m) (ω₀ : Ω) (E : EvaderAlgorithm X),
    size ω₀ i * (∑ ω ∈ Finset.univ.filter
        (fun ω => (List.ofFn (chunk ω)).take i = (List.ofFn (chunk ω₀)).take i), P ω)
      ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω => (List.ofFn (chunk ω)).take i = (List.ofFn (chunk ω₀)).take i),
        P ω * E.escapeCost (((List.ofFn (chunk ω)).take i).flatten) (chunk ω i) price
  htotal : total ≤ ∑ ω, P ω * (∑ i, size ω i)

attribute [instance] ChunkSystem.instFin ChunkSystem.instDec

/-- The flattened request sequence of an outcome. -/
def ChunkSystem.seq {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ}
    {mLo : ℕ} (C : ChunkSystem X s t cLo cHi total price mLo) (ω : C.Ω) : List (Set X) :=
  (List.ofFn (C.chunk ω)).flatten

end KServer


